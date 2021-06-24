#!/bin/bash

log3=".n3.log"
log5=".n5.log"

run_3n() {
  echo
  echo "3n"
  timeout --foreground 60s java -cp ~/bin/tla2tools.jar tlc2.TLC -config MongoRaftReconfigProofs_3n.cfg MongoRaftReconfigProofs.tla -workers 1 | tee -a $log3
  #timeout --foreground 5m java -cp ~/bin/tla2tools.jar tlc2.TLC -config MongoRaftReconfigProofs_3n.cfg MongoRaftReconfigProofs.tla -workers 8 | tee -a $log3
}

run_5n() {
  echo
  echo "5n"
  timeout --foreground 2m java -cp ~/bin/tla2tools.jar tlc2.TLC -config MongoRaftReconfigProofs_5n.cfg MongoRaftReconfigProofs.tla -workers 1 | tee -a $log5
  #timeout --foreground 5m java -cp ~/bin/tla2tools.jar tlc2.TLC -config MongoRaftReconfigProofs_5n.cfg MongoRaftReconfigProofs.tla -workers 8 | tee -a $log5
}


rm -f $log3 $log5
touch $log3 $log5

for i in `seq 2`
do
  echo
  echo "TRIAL $i"
  run_3n
  num_violations=$(grep 'violated' $log3 | wc -l)
  if [[ $num_violations -gt 0 ]]
  then
    break
  fi

  #run_5n
  #echo
  #num_violations=$(grep 'violated' $log5 | wc -l)
  #if [[ $num_violations -gt 0 ]]
  #then
    #break
  #fi
done

num_states3=$(grep 'Finished computing initial states:' $log3 | sed 's/Finished computing initial states: //g' | sed 's/ distinct states generated.*$//g' | awk '{total+=$1} END {print total}')
num_states5=$(grep 'Finished computing initial states:' $log5 | sed 's/Finished computing initial states: //g' | sed 's/ distinct states generated.*$//g' | awk '{total+=$1} END {print total}')
num_violations3=$(grep 'violated' $log3 | wc -l)
num_violations5=$(grep 'violated' $log5 | wc -l)
rm -f $log3 $log5

echo "Checked a total of $num_states3 initial states for 3n"
echo "Checked a total of $num_states5 initial states for 5n"
echo "Found $num_violations3 violations for 3n"
echo "Found $num_violations5 violations for 5n"
