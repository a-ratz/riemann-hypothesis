import Main
/-! Give every theorem and definition of the chosen modules back to the kernel, from this file,
which is not a `module`, so every definition is visible to the kernel (as in an export replay).

Each constant `c` is re-added as a fresh constant `_recheck.c` with the same type and value.
Env vars: RECHECK_OUT (output file), RECHECK_SHARD / RECHECK_SHARDS (which part to check),
RECHECK_ROOTS (module roots, separated by commas; default `Lib,New,Main,Statements,TauCeti`).
The command fails if the kernel rejects a declaration. -/
open Lean Elab Command

run_cmd liftTermElabM do
  let env ← getEnv
  let some out ← IO.getEnv "RECHECK_OUT" | throwError "set RECHECK_OUT"
  let shard := ((← IO.getEnv "RECHECK_SHARD").getD "0").toNat!
  let shards := ((← IO.getEnv "RECHECK_SHARDS").getD "1").toNat!
  let roots := ((← IO.getEnv "RECHECK_ROOTS").getD "Lib,New,Main,Statements,TauCeti").splitOn ","
  let h ← IO.FS.Handle.mk out .write
  let mods := env.header.moduleNames
  let maxHb : USize := (4000000 * 1000 : Nat).toUSize
  let mut idx : Nat := 0
  let mut modules : Nat := 0
  let mut checked : Nat := 0
  let mut failed : Nat := 0
  for mi in [0:env.header.moduleData.size] do
    let m := mods[mi]!
    unless roots.contains m.getRoot.toString do continue
    modules := modules + 1
    for n in env.header.moduleData[mi]!.constNames do
      idx := idx + 1
      unless idx % shards == shard do continue
      let some ci := env.find? n | continue
      let n' := `_recheck ++ n
      let decl? : Option Declaration := match ci with
        | .thmInfo v => some (.thmDecl { v with name := n' })
        | .defnInfo v =>
          if v.safety == .safe then
            some (.defnDecl { v with name := n', all := [n'], hints := .opaque })
          else none
        | _ => none
      let some decl := decl? | continue
      checked := checked + 1
      let t0 ← IO.monoMsNow
      match env.addDeclCore maxHb (defaultMaxRecDepth.toUSize) decl none with
      | .ok _ =>
        let dt := (← IO.monoMsNow) - t0
        if dt ≥ 2000 then h.putStrLn s!"SLOW\t{dt}\t{m}\t{n}"
      | .error e =>
        failed := failed + 1
        let dt := (← IO.monoMsNow) - t0
        let msg ← (e.toMessageData {}).toString
        let msg := (msg.replace "\n" " ").take 300
        h.putStrLn s!"FAIL\t{dt}\t{m}\t{n}\t{msg}"
      h.flush
  h.putStrLn s!"DONE\tmodules {modules}\tchecked {checked}\tfailed {failed}"
  h.flush
  if failed > 0 then
    throwError "the kernel rejected {failed} of {checked} declarations; see {out}"
