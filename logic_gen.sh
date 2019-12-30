#!/bin/sh
if [ $# -eq 0 ]
then
    src=LogicGenerator/Config.v
else
    src=$1
    echo "cp ${src} LogicGenerator/Config.v"
    cp ${src} LogicGenerator/Config.v
fi
make -j7; cd LogicGenerator; rm Config.vo; make; cd ..
if [ $# -le 1 ]
then
    dst=LogicGenerator/Generated.v
else
    dst=$2
    echo "cp LogicGenerator/demo/Generated.v ${dst}"
    cp LogicGenerator/Generated.v ${dst}
fi
