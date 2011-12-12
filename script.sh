. ./setEnvs.sh
echo "INSTALLING DEPENDENCIES"
yum install gcc-c++ make glibc-static glibc-common glibc-utils binutils gcc glibc-headers git tcl-devel tk-devel  gtk2-devel 

wget http://sourceforge.net/projects/pcre/files/pcre/7.8/pcre-7.8.tar.gz/download
tar -xzvf pcre-7.8.tar.gz
cd pcre-7.8
./configure  --prefix=$PPRZ_INST_DIR
make
make install


wget http://caml.inria.fr/pub/distrib/ocaml-3.11/ocaml-3.11.2.tar.gz
./configure  -prefix $PPRZ_INST_DIR
# melding over labltk. misschien is TK nodig?
make world
make opt
make install



wget http://download.camlcity.org/download/findlib-1.2.7.tar.gz
tar -xzvf ...
./configure
make all
make opt
make install

wget http://www.math.nagoya-u.ac.jp/~garrigue/soft/olabl/dist/lablgtk-2.14.2.tar.gz
tar -xzvf ...


wget http://www.math.nagoya-u.ac.jp/~garrigue/soft/olabl/dist/lablgtk-2.14.2.tar.gz
tar -xzvf ...
./configure  --prefix=$PPRZ_INST_DIR
make
make opt
make install
ocamlfind install lablgtk2 META



wget http://tech.motion-twin.com/zip/xml-light-2.2.zip
unzip ...
make
make opt
make install

cat << EOF > META
version="2.2"
archive(byte)="xml-light.cma"
archive(native)="xml-light.cmxa"
linkopts=""
directory="+xml-light"
EOF
ocamlfind install xml-light META


wget http://hg.ocaml.info/release/pcre-ocaml/archive/b3f3e6899e80.tar.gz
#later we might want to upgrade to 6.0.1
make all
make install



#this is a newer version than on Ubuntu 1004, but it seems to work fine
wget http://download.camlcity.org/download/ocamlnet-3.4.1.tar.gz
#do stuff
./configure -enable-gtk2 -with-nethttpd 
make all
make opt
make install

