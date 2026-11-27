# Paths: set STUDY_ROOT (this repository), WORK_ROOT (folder holding ts_ws/, auditreal/, ...)
# and DISS_ROOT to override. Defaults: the repo root; E:/ on Windows, ~/work/ elsewhere; parent of the repo.
import os as _os
def _repo_root():
    d = _os.path.dirname(_os.path.abspath(__file__))
    while not _os.path.exists(_os.path.join(d, "CLOUD.md")) and _os.path.dirname(d) != d:
        d = _os.path.dirname(d)
    return d
_STUDY = _os.environ.get("STUDY_ROOT", _repo_root()).replace("\\", "/").rstrip("/")
_WR = _os.environ.get("WORK_ROOT", "E:/" if _os.name == "nt" else _os.path.expanduser("~/work")).replace("\\", "/").rstrip("/") + "/"
_DISS = _os.environ.get("DISS_ROOT", _os.path.dirname(_STUDY)).replace("\\", "/").rstrip("/") + "/"
import io
B=_WR + 'ts_ws/prove_ts/ws/lean/CmlTS/'
def sub(f,a,b):
    t=io.open(B+f,encoding='utf-8').read(); assert t.count(a)==1,(f,a,t.count(a)); io.open(B+f,'w',encoding='utf-8',newline='\n').write(t.replace(a,b))
sub('TypeSoundInvariants.lean','def ctMap_has_exns (ctMap : ctMap_ty) : Prop :=','def ctMap_has_exns {α β : Type} (ctMap : fmap stamp (List α × List β × Nat)) : Prop :=')
sub('TypeSoundInvariants.lean','def ctMap_has_bools (ctMap : ctMap_ty) : Prop :=','def ctMap_has_bools {α β : Type} (ctMap : fmap stamp (List α × List β × Nat)) : Prop :=')
sub('TypeSystem.lean','''def build_ctor_tenv (tenvT : Namespace modN typeN (List tvarN × typ)) :
    List (List tvarN × mlstring × List (conN × List ast_t)) → List type_ident → tenv_ctor
''','''def build_ctor_tenv {m n γ ε δ : Type} (tenvT : Namespace modN typeN (List tvarN × typ)) :
    List (γ × ε × List (n × List ast_t)) → List δ → Namespace m n (γ × List typ × δ)
''')
sub('TypeSysProps.lean','''    ∀ (tenvT : Namespace modN typeN (List tvarN × typ))
      (tds : List (List tvarN × mlstring × List (conN × List ast_t)))
      (tis : List type_ident),
      tds.length = tis.length ∧
      check_ctor_tenv tenvT tds ∧
      tenv_abbrev_ok tenvT →
      tenv_ctor_ok (build_ctor_tenv tenvT tds tis) := by''','''    ∀ {m δ : Type} (tenvT : Namespace modN typeN (List tvarN × typ))
      (tds : List (List tvarN × mlstring × List (conN × List ast_t)))
      (tis : List δ),
      tds.length = tis.length ∧
      check_ctor_tenv tenvT tds ∧
      tenv_abbrev_ok tenvT →
      tenv_ctor_ok (build_ctor_tenv tenvT tds tis : Namespace m conN (List tvarN × List typ × δ)) := by''')
