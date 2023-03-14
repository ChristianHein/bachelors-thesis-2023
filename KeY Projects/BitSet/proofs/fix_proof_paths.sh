#!/bin/sh

# Fix relative file paths in proof files.
#
# KeY Proof files will sometimes (always?) refer to files using bizarre
# relative paths. The paths start with a relative path to "/" (root) and then
# continue with the absolute path of the file.
#
# Examples:
#    \javaSource "../../../../../../../../../../../../../home/christianhein/Universität/Module/Bachelorarbeit/WS2223/Git Repository/KeY Projects/BitSet";
#     \include "../../../../../../../../../../../../../home/christianhein/Universität/Module/Bachelorarbeit/WS2223/Git%20Repository/KeY%20Projects/BitSet/taclets/intSet.key";
#
# This script fixes the above paths to the following:
#     \javaSource "..";
#     \include "../taclets/intSet.key";

temp_file="${XDG_CACHE_HOME}/tmpfile"

for proof_file in *.proof
do
    sed -E \
        -e 's/"[^"]*(taclets\/[^"]*\.key)"/"..\/\1"/g' \
        -e 's/^\\javaSource ".*";$/\\javaSource "..";/' \
        "${proof_file}" \
        > "${temp_file}"
    mv "${proof_file}" "${proof_file}.bak"
    mv "${temp_file}" "${proof_file}"
done

