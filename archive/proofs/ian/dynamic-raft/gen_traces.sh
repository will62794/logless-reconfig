#/bin/bash

java -cp /c/Users/ianda/bin/tla2tools.jar tlc2.TLC -config MCMongoLoglessDynamicRaftProofs.cfg -simulate file=out.txt,num=2 MongoLoglessDynamicRaftProofs.tla
