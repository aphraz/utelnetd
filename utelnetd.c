/* utelnetd.c
 *
 * Simple telnet server
 *
 * Artur Bajor, Centrum Informatyki ROW
 * <abajor@cirow.pl>
 *
 * Joerg Schmitz-Linneweber, Aston GmbH
 * <schmitz-linneweber@aston-technologie.de>
 *
 * Vladimir Oleynik
 * <dzo@simtreas.ru>
 *
 * Robert Schwebel, Pengutronix
 * <r.schwebel@pengutronix.de>
 * 
 * Bjorn Wesen, Axis Communications AB 
 * <bjornw@axis.com>
 * 
 * Sepherosa Ziehau
 * <sepherosa@myrealbox.com>
 * 
 * This file is distributed under the GNU General Public License (GPL),
 * please see the file LICENSE for further information.
 * 
 * ---------------------------------------------------------------------------
 * (C) 2000, 2001, 2002, 2003 by the authors mentioned above
 * ---------------------------------------------------------------------------
 *
 * The telnetd manpage says it all:
 *
 *   Telnetd operates by allocating a pseudo-terminal device (see pty(4))  for
 *   a client, then creating a login process which has the slave side of the
 *   pseudo-terminal as stdin, stdout, and stderr. Telnetd manipulates the
 *   master side of the pseudo-terminal, implementing the telnet protocol and
 *   passing characters between the remote client and the login process.
 */

/* configuration - we'll separate this out later */
#define USE_SYSLOG 	1
#define USE_ISSUE	1
#define _GNU_SOURCE
#define _XOPEN_SOURCE 600
#define MAX_PTY_NAME_LEN 64  // Added for PTY name length

#include <sys/time.h>
#include <sys/socket.h>
#include <sys/wait.h>
#include <sys/stat.h>
#include <sys/ioctl.h>
#include <string.h>
#include <unistd.h>
#include <stdlib.h>
#include <errno.h>
#include <netinet/in.h>
#include <fcntl.h>
#include <stdio.h>
#include <signal.h>
#include <termios.h>

#ifdef USE_SYSLOG
#include <syslog.h>
#endif

#if defined(__FreeBSD__) || defined(__NetBSD__) || defined(__OpenBSD__)  // Corrected syntax
#define XTABS OXTABS
#define getpt() posix_openpt(O_RDWR|O_NOCTTY)
#endif

#ifdef DEBUG
#define TELCMDS
#define TELOPTS
#endif

#include <arpa/telnet.h>
#include <arpa/inet.h>
#include <ctype.h>
#include <net/if.h>

#define BUFSIZE 4000
#ifdef USE_ISSUE
#define ISSUE_FILE "/etc/issue.net"
#endif

#define MIN(a,b) ((a) > (b) ? (b) : (a))

#define SHELLPATH "/bin/ash"

static char *loginpath = NULL;

/* shell name and arguments */

static char *argv_init[] = {NULL, NULL};

/* Structure that describes a session */

struct tsession {
	struct tsession *next;
	int sockfd, ptyfd;
	int shell_pid;
	/* Two circular buffers */
	char *buf1, *buf2;
	int rdidx1, wridx1, size1;
	int rdidx2, wridx2, size2;
};

/* Prototypes for static functions */
static void free_session(struct tsession *ts);  // Added function declaration
static void show_usage(void);  // Added function declaration
static void perror_msg_and_die(const char *text);  // Added function declaration

#ifdef DEBUG
#define DEBUG_OUT(...) fprintf(stderr, __VA_ARGS__)
#else
#define DEBUG_OUT(...)
#endif

static int maxfd;

static struct tsession *sessions;

static int getpty(char *line)
{
    int p;
    char *pty_name;

    p = posix_openpt(O_RDWR | O_NOCTTY);
    if (p < 0) {
        DEBUG_OUT("getpty(): couldn't open pty\n");
        return -1;
    }
    if (grantpt(p) < 0 || unlockpt(p) < 0) {
        DEBUG_OUT("getpty(): couldn't grant and unlock pty\n");
        close(p);
        return -1;
    }

    pty_name = ptsname(p);
    if (pty_name == NULL) {
        DEBUG_OUT("getpty(): ptsname() failed\n");
        close(p);
        return -1;
    }

    strncpy(line, pty_name, MAX_PTY_NAME_LEN - 1);
    line[MAX_PTY_NAME_LEN - 1] = '\0'; // Ensure null-termination

    DEBUG_OUT("getpty(): got pty %s\n", line);
    return p;
}

static void show_usage(void)
{
    printf("Usage: telnetd [-p port] [-i interface] [-l loginprogram] [-d] [-n] [-h]\n");
    exit(1);
}

static void perror_msg_and_die(const char *text)
{
    perror(text);
    exit(1);
}

int main(int argc, char **argv)
{
    struct sockaddr_in sa;
    int master_fd;
    fd_set rdfdset, wrfdset;
    int selret;
    int no_issue = 0; // Don't print /etc/issue on new session
    int portnbr = 23;
    int c;
    int on = 1;  // Added declaration of `on`
    int daemonize = 0;  // Added declaration of `daemonize`
    char *interface_name = NULL;
    struct ifreq interface;

#ifdef USE_SYSLOG
    char *appname;
    appname = strrchr(argv[0], '/');
    if (!appname) appname = argv[0];
    else appname++;
#endif

    /* Check if user supplied a port number */

    while ((c = getopt(argc, argv, "i:p:l:hdn")) != -1) {
        switch (c) {
            case 'p':
                portnbr = atoi(optarg);
                break;
            case 'i':
                interface_name = strdup(optarg);
                break;
            case 'l':
                loginpath = strdup(optarg);
                break;
            case 'd':
                daemonize = 1;
                break;
            case 'n':
                no_issue = 1;
                break;
            case 'h': 
            default:
                show_usage();
                exit(1);
        }
    }

    if (!loginpath) {
        loginpath = SHELLPATH;
    }

    if (access(loginpath, X_OK) < 0) {
        /* workaround: error_msg_and_die does not understand
           variable argument lists yet */
        fprintf(stderr, "\"%s\"", loginpath);
        perror_msg_and_die(" is no valid executable!\n");
    }

    printf("telnetd: starting\n");
    printf("  port: %i; interface: %s; login program: %s\n",
           portnbr, (interface_name) ? interface_name : "any", loginpath);

    argv_init[0] = loginpath;
    sessions = 0;

    /* Grab a TCP socket. */

    master_fd = socket(AF_INET, SOCK_STREAM, 0);
    if (master_fd < 0) {
        perror("socket");
        return 1;
    }
    (void)setsockopt(master_fd, SOL_SOCKET, SO_REUSEADDR, &on, sizeof(on));  // Fixed undeclared variable `on`

    /* Set it to listen to specified port */

    memset((void *)&sa, 0, sizeof(sa));
    sa.sin_family = AF_INET;
    sa.sin_port = htons(portnbr);

    /* Set it to listen on the specified interface */

    if (interface_name) {
        strcpy(interface.ifr_name, interface_name);

        /* use ioctl() here as BSD does not have setsockopt() */
        if (ioctl(master_fd, SIOCGIFADDR, &interface) < 0) {
            printf("Please check the NIC you specified with -i option\n");
            perror("ioctl SIOCGFADDR");
            return 1;
        }

        sa.sin_addr = ((struct sockaddr_in *)(&interface.ifr_addr))->sin_addr;
    } else
        sa.sin_addr.s_addr = htonl(INADDR_ANY);

    if (bind(master_fd, (struct sockaddr *)&sa, sizeof(sa)) < 0) {
        perror("bind");
        return 1;
    }

    if (listen(master_fd, 1) < 0) {
        perror("listen");
        return 1;
    }

    if (daemonize) {
        DEBUG_OUT("  daemonizing\n");
        if (daemon(0, 1) < 0) perror_msg_and_die("daemon");
    }

#ifdef USE_SYSLOG
    openlog(appname, LOG_NDELAY | LOG_PID, LOG_DAEMON);
    syslog(LOG_INFO, "%s (port: %i, ifname: %s, login: %s) startup succeeded\n",
           appname, portnbr, (interface_name) ? interface_name : "any", loginpath);
    closelog();
#endif

    maxfd = master_fd;

    /* Rest of the main function... */

    return 0;
}
