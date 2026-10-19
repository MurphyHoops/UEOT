import Lake
open Lake DSL

package ueot_qm where
  version := v!"1.0.0"

require ueot_core from "../ueot-core"

@[default_target]
lean_lib UEOTQM

