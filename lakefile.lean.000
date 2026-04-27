import Lake
open Lake DSL

package «siat» where
  -- Add any extra package configuration here

@[default_target]
lean_lib «Siat» where
  -- Tells Lake to look in the root folder for your .lean files
  srcDir := "."
  -- Explicitly defines the modules to be built
  roots := #[`Bedrock, `Invariance, `Main, `Main_Standalone]

-- Required dependency for Mathlib
require mathlib from git
  "https://github.com"

-- Required for auto-generating the documentation website via GitHub Actions
meta if get_config? env = some "dev" then
  require «doc-gen4» from git "https://github.com" @ "main"
