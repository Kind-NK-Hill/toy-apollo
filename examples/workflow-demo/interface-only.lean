-- Teaching fixture: the definition is repaired but its caller is still old.
def def_demo_frequency (hits total : Nat)
    (_positive : 0 < total) (_bounded : hits <= total) : Nat :=
  1000 * hits / total

theorem demo_two_of_four : def_demo_frequency 2 4 = 500 := by decide
