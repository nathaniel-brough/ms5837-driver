FROM gcr.io/oss-fuzz-base/base-builder-rust

COPY . $SRC/ms5837-driver                     
WORKDIR $SRC/ms5837-driver                 
COPY ./.clusterfuzzlite/build.sh $SRC/  