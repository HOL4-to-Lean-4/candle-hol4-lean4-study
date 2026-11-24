"""Write the Lean file that proves the two pilot decoys equivalent to the originals."""
import io, re
src = io.open("E:/auditwork/9a48a4cb/lean/CandleLean/HolSyntax.lean", encoding="utf-8").read()
d = re.search(r"^def term_lt \(a b.*?term_lt' a b\n", src, re.M | re.S).group(0).replace("def term_lt (", "def term_lt_decoy (", 1)
out = """import CandleLean
open HOL Classical
namespace Candle
example : (∀ ls : List string, ALL_DISTINCT ls → ALL_DISTINCT (List.map implode ls)) =
    (∀ ls : List string, ALL_DISTINCT ls → ALL_DISTINCT (List.map (fun x_e => implode x_e) ls)) := rfl

""" + d + """
theorem decoy_eq : @term_lt_decoy = @term_lt := by
  funext a b
  apply propext
  constructor
  · intro h R ⟨h1, h2, h3, h4, h5, h6, h7⟩
    exact h R ⟨h1, h2, h3, h4, h5, fun a b => h6 b a, h7⟩
  · intro h R ⟨h1, h2, h3, h4, h5, h6, h7⟩
    exact h R ⟨h1, h2, h3, h4, h5, fun a b => h6 b a, h7⟩
#print axioms decoy_eq
end Candle
"""
io.open("E:/ts_ws/mut_work/stripped/DecoyPilot.lean", "w", encoding="utf-8", newline="\n").write(out)
