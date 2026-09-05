-- Teaching fixture: the required domain conditions are missing.
def def_demo_frequency (hits total : Nat) : Nat := 1000 * hits / total

theorem demo_two_of_four : def_demo_frequency 2 4 = 500 := by decide
