#!/bin/bash
export PPPZ_BASEDIR=dirname $(readlink -f $0)
echo $PPPZ_BASEDIR
