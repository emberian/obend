import Lake
open Lake DSL System

package vaultsync

input_file vaultSyncSource where
  path := "vault_sync.c"

target vaultSyncO pkg : FilePath := do
  buildO (pkg.buildDir / "vault_sync.o") (← vaultSyncSource.fetch)
    #["-I", (← getLeanIncludeDir).toString] #["-fPIC"]
