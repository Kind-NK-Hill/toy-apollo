-- Teaching fixture: the domain contract and its caller agree.
def def_demo_frequency (hits total : Nat)
    (_positive : 0 < total) (_bounded : hits <= total) : Nat :=
  1000 * hits / total

theorem demo_two_of_four :
    def_demo_frequency 2 4 (by decide) (by decide) = 500 := by decide
