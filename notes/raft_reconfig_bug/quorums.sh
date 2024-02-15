#!/bin/bash
tlc="/Users/willyschultz/Downloads/zulu15.32.15-ca-jdk15.0.3-macosx_aarch64/bin/java -DTLA-Library=/usr/local/lib/tlaps -cp /usr/local/tla2tools-v1.8.jar tlc2.TLC"
$tlc -noGenerateSpecTE -dump dot,colorize,actionlabels quorums.dot quorums
sed -E -i "" "s/.*rank.*;}//" quorums.dot
dot -Tpdf quorums.dot > quorums.pdf