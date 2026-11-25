import Lake
open Lake DSL

package «cml_ts» where

require batteries from git "https://github.com/leanprover-community/batteries" @ "v4.28.0"

@[default_target]
lean_lib «CmlTS» where
