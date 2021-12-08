#!/bin/sh

#
# Archives files needed to automatically prove our theorems for the CPP submission
#

source_dir=$(dirname "${BASH_SOURCE[0]}")
pushd "$source_dir" &>/dev/null
folder_root=$(pwd | sed 's|logless-reconfig/.*$|logless-reconfig|g')
popd &>/dev/null

target="$folder_root/archive/cpp2022"
mkdir -p "$folder_root/archive"
rm -rf "$target"
mkdir "$target"

cp "$folder_root/MongoLoglessDynamicRaft.tla" "$target"
cp "$folder_root/MongoRaftReconfig.tla" "$target"
cp "$folder_root/MongoStaticRaft.tla" "$target"
cp "$folder_root/proofs/AuxLemmas.tla" "$target"
cp "$folder_root/proofs/Assumptions.tla" "$target"
cp "$folder_root/proofs/BasicQuorumsLib.tla" "$target"
cp "$folder_root/proofs/ElectionSafetyLemmas.tla" "$target"
cp "$folder_root/proofs/LeaderCompletenessLemmas.tla" "$target"
cp "$folder_root/proofs/LeaderCompletenessLib.tla" "$target"
cp "$folder_root/proofs/Lib.tla" "$target"
cp "$folder_root/proofs/LogLemmas.tla" "$target"
cp "$folder_root/proofs/MongoRaftReconfigIndInv.tla" "$target"
cp "$folder_root/proofs/MongoRaftReconfigProofs.tla" "$target"
cp "$folder_root/proofs/MongoRaftReconfigRefinementProofs.tla" "$target"
cp "$folder_root/proofs/README.md" "$target"
cp "$folder_root/proofs/StateMachineSafetyLemmas.tla" "$target"
cp "$folder_root/proofs/TypeOK.tla" "$target"
cp "$folder_root/scripts/checkproofs.sh" "$target"

git_head_rev=`git rev-parse --short HEAD`
zip_target="$folder_root/archive/cpp2022_$git_head_rev.tar.gz"
rm -f "$zip_target"
tar -zcvf "$zip_target" "$target" &>/dev/null

rm -rf "$target"
