cd ~/ts_build
for c in locnrow locncol locn_rowupdate locn_colupdate MAP3 dest_Refv FV_dec type_def_to_ctMap the_Litv_IntLit the_Litv_Word8 the_Litv_Word64 the_Litv_Float64 the_Litv_Char closest_such; do
  echo "== $c"; grep -rlE "val ${c}(_def|_DEF)?(_primitive)?(_def)? *:" --include=*Theory.sig . | head -3
  grep -rhoE "val ${c}[A-Za-z_]*primitive[A-Za-z_]* *:" --include=*Theory.sig . | sort -u
done
H=$(find ~ -maxdepth 4 -name "listTheory.sig" 2>/dev/null | head -1); echo $H
for d in $(dirname "$H") ; do grep -hE "val (HD|THE|EL|LAST)[A-Za-z_]*(primitive|PRIM)[A-Za-z_]*" $d/*.sig; grep -hE "val HD[_A-Za-z]* *:" $d/listTheory.sig; done
find ~ -name optionTheory.sig | head -1 | xargs grep -nE "val THE[_A-Za-z]* *:"
