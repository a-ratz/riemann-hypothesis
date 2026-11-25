/-! Trial file for the risky-constructs workflow. Not part of the proof. -/
theorem a (p : Prop) : p := by grind +trace
theorem b (p : Prop) : p := by
  grind => finish?
theorem c (p : Prop) : p := by lia (trace := .true)
#guard_msgs (drop error) in
theorem d : False := by rfl
@[init] def e : IO Unit := pure ()
theorem f : False := by sorry
