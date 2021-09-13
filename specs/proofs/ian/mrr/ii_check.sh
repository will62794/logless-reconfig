#!/bin/bash

#java -cp ~/bin/tla2tools.jar tlc2.TLC -config MongoRaftReconfigProofs_3n.cfg MongoRaftReconfigProofs.tla -workers 1
java -cp ~/bin/tla2tools.jar tlc2.TLC -config MongoRaftReconfigProofsAlternate_3n.cfg MongoRaftReconfigProofsAlternate.tla -workers 1
