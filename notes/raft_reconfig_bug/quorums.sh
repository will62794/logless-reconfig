#!/bin/bash
tlc="/Users/willyschultz/Downloads/zulu15.32.15-ca-jdk15.0.3-macosx_aarch64/bin/java -DTLA-Library=/usr/local/lib/tlaps -cp /usr/local/tla2tools-v1.8.jar tlc2.TLC"

# For loop iterating over strings.
for name in "quorums_n2" "quorums_n3" "quorums_n4" "quorums_n5"
do
  $tlc -noGenerateSpecTE -config $name.cfg -dump dot,colorize $name.dot quorums
  sed -E -i "" "s/.*rank.*;}//" $name.dot
  sed -E -i "" "s/.*rank.*;}//" $name.dot
  sed -E -i "" "s/nodesep=0.35;/nodesep=0.35;concentrate=false;/" $name.dot
  # Render standard.
  dot -Tpng -Gdpi=200 -Gconcentrate=true $name.dot > $name.png

  # Remove the legend for fdp.
  sed -E -i "" "s/SingleNodeChange.*//" $name.dot
  sed -E -i "" "s/ToQuorumOverlap.*//" $name.dot

  # Render with force-directed.
  dot -Tpng -Ksfdp -Gdpi=180 -Gnodesep=0.065 -Gconcentrate=false $name.dot > ${name}_fdp.png
done
