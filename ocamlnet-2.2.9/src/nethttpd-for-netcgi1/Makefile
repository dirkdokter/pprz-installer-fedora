TOP_DIR=../..

PKGNAME  = nethttpd-for-netcgi1
OBJECTS  = nethttpd_types.cmo nethttpd_kernel.cmo nethttpd_reactor.cmo \
	  nethttpd_engine.cmo nethttpd_services.cmo nethttpd_plex.cmo

DOBJECTS = nethttpd_types.mli nethttpd_kernel.mli nethttpd_reactor.mli \
	  nethttpd_engine.mli nethttpd_services.mli nethttpd_plex.mli

INCLUDES += $(INC_EQUEUE) $(INC_NETSTRING) $(INC_NETCGI1) $(INC_NETPLEX)
PP_OPTIONS = -package "camlp4, camlp4.macro" -syntax "camlp4o"

#PP_OPTIONS_FINDLIB += -ppopt "-DTesting"
# do this to enable test coverage calculations

include $(TOP_DIR)/Makefile.rules

include depend
