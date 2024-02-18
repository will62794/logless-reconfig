#!/bin/bash
tlc="/Users/willyschultz/Downloads/zulu15.32.15-ca-jdk15.0.3-macosx_aarch64/bin/java -DTLA-Library=/usr/local/lib/tlaps -cp /usr/local/tla2tools-v1.8.jar tlc2.TLC"

# For loop iterating over strings.
for name in "quorums_n2" "quorums_n3" "quorums_n4" "quorums_n5"
do
  $tlc -noGenerateSpecTE -config $name.cfg -dump dot,colorize $name.dot quorums
  sed -E -i "" "s/.*rank.*;}//" $name.dot
  sed -E -i "" "s/.*rank.*;}//" $name.dot
  # Render standard.
  dot -Tpng -Gdpi=180 -Gconcentrate=true $name.dot > $name.png

  # Remove the legend for fdp.
  sed -E -i "" "s/SingleNodeChange.*//" $name.dot
  sed -E -i "" "s/ToQuorumOverlap.*//" $name.dot

  # Render with force-directed.
  # command line flag to remove all arrowheads: 
  # Set edge style from command line flag: 

  nodesep="0.15"
  # If "quorums_n2" then make nodesep=0.3
  if [ $name = "quorums_n2" ]
  then
      nodesep="0.35"
  fi

  dot -Tpng -Kneato -Gdpi=180 -Gnodesep=$nodesep -Epenwidth=0.7 -Goverlap=scale -Gconcentrate=false $name.dot > ${name}_neato.png
  dot -Tpng -Ksfdp -Gdpi=180 -Gnodesep=$nodesep -Epenwidth=0.7 -Goverlap=scale -Gconcentrate=false $name.dot > ${name}_fdp.png
done
