import Lake
open Lake DSL

package «candle_lean» where

require batteries from git "https://github.com/leanprover-community/batteries" @ "v4.28.0"

@[default_target]
lean_lib «CandleLean» where
