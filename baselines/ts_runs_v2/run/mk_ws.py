import io,os,json,re,shutil,sys
B='E:/NUS/mcomp/Dissertation/candle_study/baselines/'
C='E:/ts_ws/common/'; mods=json.load(open(C+'mods.json')); order=mods['order']; MOD=mods['mod']
def sub(t,pairs):
    for a,b in pairs:
        assert a in t,(a[:70]); t=t.replace(a,b)
    return t
modlist=','.join(MOD[o] for o in order)
def stage1(src):
    t=io.open(src,encoding='utf-8').read()
    i=t.index("- `hol4/package/`: the HOL4 sources"); j=t.index("- `hol4/HOL4-src/`")
    t=t[:i]+"- `hol4/package/`: the HOL4 sources, 20 theory scripts (`*Script.sml`) and `preamble.sml`.\n"+t[j:]
    i=t.index("- `TARGETS.tsv`: the declarations in scope"); j=t.index("- `lean/`: a Lean 4.28.0 Lake project")
    t=t[:i]+"""- `TARGETS.tsv`: the declarations in scope, one per line (kind, theory, name, script, line).
  It lists the 267 target theorems (for stage 2), 255 definitions, 4 inductive relations and 56
  datatypes. These are a minimum: also translate every other package definition, inductive
  relation, type abbreviation or overload, and every HOL4 library constant, that a target
  theorem statement or a translated definition mentions. Read the 267 target statements to
  find those.
"""+t[j:]
    t=re.sub(r"- `lean/`: a Lean 4\.28\.0 Lake project.*?and the root `CandleLean\.lean` importing them\.","- `lean/`: a Lean 4.28.0 Lake project, package `cml_ts`, with Batteries as its only\n  dependency (already built). It has one empty module per theory:\n  `CmlTS/{"+modlist+"}.lean`\n  and the root `CmlTS.lean` importing them.",t,flags=re.S)
    t=sub(t,[("a reduced HOL4 development (CakeML's\nCandle kernel soundness theorem `holSoundness.proves_sound`)","a reduced HOL4 development (the CakeML\ntype soundness theorem `typeSound.semantics_type_sound`)"),
             ("the 278 theorem statements","the 267 theorem statements"),("Do not write the 278 target theorems","Do not write the 267 target theorems"),("existing Lean translations of CakeML or\n   Candle","existing Lean translations of CakeML")])
    return common(t)
def stage2(src):
    t=io.open(src,encoding='utf-8').read()
    t=sub(t,[("development (CakeML's Candle kernel soundness theorem `holSoundness.proves_sound`) into Lean 4.","development (the CakeML type soundness theorem `typeSound.semantics_type_sound`) into Lean 4."),
             ("the HOL4 sources (10 theories)","the HOL4 sources (20 theories)"),("Do not look for existing Lean translations of CakeML or Candle anywhere","Do not look for existing Lean translations of CakeML anywhere")])
    return common(t)
def common(t):
    t=t.replace("CandleLean.HolSyntaxExtra","CmlTS.TypeSystem").replace("CandleLean.Misc","CmlTS.Misc").replace("CandleLean","CmlTS").replace("`/home/claude/work/ws/`","your working directory").replace("all inside your working directory","all inside your working directory")
    t=re.sub(r"Do not read any other path on this\s+machine \(.*?\)\.","Do not read any other path on this machine.",t,flags=re.S)
    i=t.index("## Environment"); j=t.index("## Final report")
    t=t[:i]+"""## Environment

Your tools are Read, Write, Edit, Glob, Grep and Bash. Bash runs only `lake build ...`,
`lake env lean ...`, `cd lean`, `ls` and `date -u ...`; everything else is refused. Use Glob and
Grep to search, and Read to read. Never chain commands with pipes or redirections.

- From `lean/`: `lake build CmlTS.Misc` builds one module, `lake build` builds all.
- Quick checks: a scratch file `lean/scratch/T.lean` that imports built modules, checked with
  `lake env lean scratch/T.lean`. Keep it out of `lakefile.lean`.
- The PC is shared with other runs: one Lean process at a time, and use command timeouts.

"""+t[j:]
    t=re.sub(r"\n.*4 cores and 15 GB.*\n.*\n?","\n",t) if '4 cores' in t else t
    return t
os.makedirs(C+'briefs',exist_ok=True)
for arm,src in(('lessons','opus55_direct_translation'),('nolessons','opus55_nolessons')):
    for s,f in((1,stage1),(2,stage2)):
        t=f(B+src+f'/run/BRIEF_stage{s}.md')
        left=[w for w in('Candle','candle','278','/home/claude','holSound','CandleLean') if w in t]
        io.open(C+f'briefs/{arm}_stage{s}.md','w',encoding='utf-8',newline='\n').write(t)
        print(arm,s,len(t),left)

# ---- workspaces ----
def restore(t):
    return t.replace("Keep it out of `lakefile.lean`.","Use `#eval`/`#reduce`/`example` to test definitions on small\n  inputs where that helps you check faithfulness.")
for n in os.listdir(C+'briefs'):
    p=C+'briefs/'+n; s=io.open(p,encoding='utf-8').read(); io.open(p,'w',encoding='utf-8',newline='\n').write(restore(s) if 'stage1' in n else s)
PKG='E:/NUS/mcomp/Dissertation/typesound_lean4_sorry/hol4-ultramin'
PKGLIB='E:/ts_ws/real/opus55_direct_translation/.lake'
SETTINGS={"permissions":{"allow":["Read(./**)","Edit(./**)","Write(./**)","Read(~/.elan/toolchains/leanprover--lean4---v4.28.0/**)","Glob","Grep","Bash(lake build:*)","Bash(lake env lean:*)","Bash(cd lean)","Bash(date -u:*)","Bash(ls:*)"],"deny":["Read(//e/NUS/**)","Edit(//e/NUS/**)","Read(~/.claude/**)","Read(~/.codex/**)","WebFetch","WebSearch","Task","Agent","Bash(git:*)","Bash(curl:*)","Bash(wget:*)","Bash(gh:*)"]}}
def make(run):
    d='E:/ts_ws/runs/'+run+'/ws1'
    assert not os.path.exists(d),d
    os.makedirs(d+'/hol4'); shutil.copytree(PKG,d+'/hol4/package',ignore=shutil.ignore_patterns('Holmakefile','LICENSE'))
    shutil.copytree('E:/ts_ws/hol4src',d+'/hol4/HOL4-src')
    shutil.copy(C+'TARGETS.tsv',d)
    L=d+'/lean'; os.makedirs(L+'/CmlTS'); 
    shutil.copy(B+'opus55_direct_translation/lean/lean-toolchain',L)
    io.open(L+'/lakefile.lean','w',newline='\n').write('import Lake\nopen Lake DSL\n\npackage «cml_ts» where\n\nrequire batteries from git "https://github.com/leanprover-community/batteries" @ "v4.28.0"\n\n@[default_target]\nlean_lib «CmlTS» where\n')
    m=json.load(open(B+'opus55_direct_translation/lean/lake-manifest.json')); m['name']='cml_ts'; json.dump(m,open(L+'/lake-manifest.json','w'),indent=1)
    shutil.copytree(PKGLIB+'/packages',L+'/.lake/packages')
    for o in order: io.open(f'{L}/CmlTS/{MOD[o]}.lean','w',newline='\n').write('')
    io.open(L+'/CmlTS.lean','w',newline='\n').write(''.join(f'import CmlTS.{MOD[o]}\n' for o in order))
    json.dump(SETTINGS,open(d+'/../settings.json','w'),indent=1)
if len(sys.argv)>1:
    for r in sys.argv[1:]: make(r)
