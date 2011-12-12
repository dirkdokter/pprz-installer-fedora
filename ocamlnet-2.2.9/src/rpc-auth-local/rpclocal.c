/* $Id: rpclocal.c 919 2006-06-15 12:32:17Z gerd $
 * ----------------------------------------------------------------------
 *
 */

#include "caml/mlvalues.h"
#include "caml/alloc.h"
#include "caml/memory.h"
#include "caml/fail.h"
#include <unistd.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <sys/un.h>
#include <sys/uio.h>
#include <string.h>
#include <stdio.h>
#include <limits.h>

/**********************************************************************/
/* From unixsupport.h                                                 */
/**********************************************************************/

#define Nothing ((value) 0)

extern void unix_error (int errcode, char * cmdname, value arg) Noreturn;
extern void uerror (char * cmdname, value arg) Noreturn;

/**********************************************************************/

value unix_get_peer_credentials(value fd) {
    CAMLparam1(fd);
    CAMLlocal1(result);
    int uid;
    int gid;

#ifdef SO_PEERCRED
    /* Linux */
    {
	socklen_t len;
	struct ucred credentials;

	len = sizeof(struct ucred);
	if (getsockopt(Int_val(fd),
		       SOL_SOCKET,
		       SO_PEERCRED,
		       &credentials,
		       &len) == -1) {
	    uerror("getsockopt",Nothing);
	};
	uid = credentials.uid;       /* Effective user ID */
	gid = credentials.gid;       /* Effective group ID */
    }
#else
    /* FreeBSD: Seems to use socket option LOCAL_PEERCRED. I have currently
     * no system to test it.
     */

    invalid_argument("get_peer_credentials");
#endif

    /* Allocate a pair, and put the result into it: */
    result = alloc_tuple(2);
    Store_field(result, 0, Val_int(uid));
    Store_field(result, 1, Val_int(gid));

    CAMLreturn(result);
}

/**********************************************************************/

/*
 * Another way of getting the credentials is too peek the next message
 * and look at the ancillary data. But this works only if the sender
 * has set the ancillary data, or if the operating system supports that
 * the receiver can request credentials.
 */

value unix_peek_peer_credentials(value fd) {
    CAMLparam1(fd);
    CAMLlocal1(result);
    int uid;
    int gid;

#ifdef SO_PASSCRED
    /* Linux */
    {
	int one = 1;
        struct msghdr msg;
        struct cmsghdr *cmp;
        struct ucred *sc;
	char buf[CMSG_SPACE(sizeof(*sc))];
	struct iovec iov;
	char iovbuf[1];

	if (setsockopt(Int_val(fd),
		       SOL_SOCKET,
		       SO_PASSCRED,
		       &one,
		       sizeof(one)) < 0) {
	    uerror("setsockopt", Nothing);
	};

	memset(&msg, 0, sizeof msg);

	msg.msg_name = NULL;
	msg.msg_namelen = 0;
	msg.msg_iov = &iov;
	msg.msg_iovlen = 1;
	msg.msg_control = buf;
	msg.msg_controllen = sizeof(buf);

	iov.iov_base = iovbuf;
	iov.iov_len = 1;

	/* Linux requires that at least one byte must be transferred.
	 * So we initialize the iovector for exactly one byte.
	 */

	if (recvmsg(Int_val(fd), &msg, MSG_PEEK) < 0) {
	    uerror("recvmsg", Nothing);
	};

	if (msg.msg_controllen == 0 ||
	    (msg.msg_flags & MSG_CTRUNC) != 0) {
	    raise_not_found();
	};
	cmp = CMSG_FIRSTHDR(&msg);
	if (cmp->cmsg_level != SOL_SOCKET ||
	    cmp->cmsg_type != SCM_CREDENTIALS) {
	    raise_not_found();
	};

	sc = (struct ucred *) CMSG_DATA(cmp);

	uid = sc->uid;
	gid = sc->gid;
    }
#else
#ifdef LOCAL_CREDS
    /* NetBSD */
    /* The following code has been copied from libc: rpc/svc_vc.c
     * TODO: The following code does not work. No idea why.
     * msg_controllen is always 0. Maybe the socket option must be
     * set earlier (but that would be very strange).
     */
    {
	int one = 1;
        struct msghdr msg;
        struct cmsghdr *cmp;
        void *crmsg = NULL;
        struct sockcred *sc;
        socklen_t crmsgsize;
	struct iovec iov;
	char buf;

	if (setsockopt(Int_val(fd),
		       SOL_SOCKET,
		       LOCAL_CREDS,
		       &one,
		       sizeof(one)) < 0) {
	    uerror("setsockopt", Nothing);
	};

	memset(&msg, 0, sizeof msg);
	crmsgsize = CMSG_SPACE(SOCKCREDSIZE(NGROUPS_MAX));
	crmsg = stat_alloc(crmsgsize);

	memset(crmsg, 0, crmsgsize);
	msg.msg_control = crmsg;
	msg.msg_controllen = crmsgsize;
	msg.msg_iov = &iov;
	msg.msg_iovlen = 1;

	iov.iov_base = &buf;
	iov.iov_len = 1;

	if (recvmsg(Int_val(fd), &msg, MSG_PEEK) < 0) {
	    stat_free(crmsg);
	    uerror("recvmsg", Nothing);
	};

	if (msg.msg_controllen == 0 ||
	    (msg.msg_flags & MSG_CTRUNC) != 0) {
	    stat_free(crmsg);
	    raise_not_found();
	};
	cmp = CMSG_FIRSTHDR(&msg);
	if (cmp->cmsg_level != SOL_SOCKET ||
	    cmp->cmsg_type != SCM_CREDS) {
	    stat_free(crmsg);
	    raise_not_found();
	};

	sc = (struct sockcred *)(void *)CMSG_DATA(cmp);

	uid = sc->sc_euid;
	gid = sc->sc_egid;
	free(crmsg);
    }
#else
    invalid_argument("peek_peer_credentials");
#endif
#endif

    /* Allocate a pair, and put the result into it: */
    result = alloc_tuple(2);
    Store_field(result, 0, Val_int(uid));
    Store_field(result, 1, Val_int(gid));

    CAMLreturn(result);
}
