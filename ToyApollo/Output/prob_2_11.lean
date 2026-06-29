import ToyApollo.Output.def_2_8

/--
PROBLEM
\textbf{2.11.} Verify that the Cantor set is a Borel set.
-/
theorem prob_2_11 : MeasurableSet (cantorSet : Set ℝ) :=
  isClosed_cantorSet.measurableSet
