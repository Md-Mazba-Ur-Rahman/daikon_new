#!/bin/bash

TARGET=Tiny

javac -g $TARGET.java
java -cp .:$DAIKONDIR/daikon.jar daikon.DynComp $TARGET
java -cp .:$DAIKONDIR/daikon.jar daikon.Chicory --daikon \
     --comparability-file=$TARGET.decls-DynComp \
     $TARGET
java -cp .:$DAIKONDIR/daikon.jar daikon.Chicory \
     --comparability-file=$TARGET.decls-DynComp \
     $TARGET
