#!/bin/sh

#
# Create a zip archive of the Git repo suitable for submission/distribution.
#

git_head_rev=`git rev-parse --short HEAD`
git archive --format=zip --output=archive/logless-reconfig_$git_head_rev.zip HEAD