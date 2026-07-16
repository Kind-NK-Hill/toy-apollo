/-
TASK ID: ex_4_4_2
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.def_4_4_complex_random_variable

open MeasureTheory
open scoped Matrix

def skewSymmetricMatrix (x : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(0 : ℂ), (x : ℂ); -(x : ℂ), 0]

def skewSymmetricCharacteristicMatrix (x : ℝ) (lam : ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  !![-lam, (x : ℂ); -(x : ℂ), -lam]

theorem skewSymmetricMatrix_transpose (x : ℝ) :
    (skewSymmetricMatrix x).transpose = -skewSymmetricMatrix x := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [skewSymmetricMatrix]

theorem skewSymmetricCharacteristicMatrix_eq_sub_scalar (x : ℝ) (lam : ℂ) :
    skewSymmetricCharacteristicMatrix x lam =
      skewSymmetricMatrix x - lam • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [skewSymmetricMatrix, skewSymmetricCharacteristicMatrix]

theorem skewSymmetricCharacteristicMatrix_det (x : ℝ) (lam : ℂ) :
    (skewSymmetricCharacteristicMatrix x lam).det =
      lam ^ 2 + (x : ℂ) ^ 2 := by
  simp [skewSymmetricCharacteristicMatrix, Matrix.det_fin_two_of]
  ring

noncomputable def skewSymmetricCharacteristicPolynomial (x : ℝ) : Polynomial ℂ :=
  Polynomial.X ^ 2 + Polynomial.C ((x : ℂ) ^ 2)

theorem skewSymmetricCharacteristicPolynomial_eval (x : ℝ) (lam : ℂ) :
    (skewSymmetricCharacteristicPolynomial x).eval lam =
      (skewSymmetricCharacteristicMatrix x lam).det := by
  calc
    (skewSymmetricCharacteristicPolynomial x).eval lam =
        lam ^ 2 + (x : ℂ) ^ 2 := by
      simp [skewSymmetricCharacteristicPolynomial]
    _ = (skewSymmetricCharacteristicMatrix x lam).det :=
      (skewSymmetricCharacteristicMatrix_det x lam).symm

theorem positiveImaginaryEigenvalue_root (x : ℝ) :
    Polynomial.IsRoot (skewSymmetricCharacteristicPolynomial x)
      (Complex.I * (x : ℂ)) := by
  rw [Polynomial.IsRoot.def]
  calc
    (skewSymmetricCharacteristicPolynomial x).eval (Complex.I * (x : ℂ)) =
        (skewSymmetricCharacteristicMatrix x (Complex.I * (x : ℂ))).det :=
      skewSymmetricCharacteristicPolynomial_eval x _
    _ = (Complex.I * (x : ℂ)) ^ 2 + (x : ℂ) ^ 2 :=
      skewSymmetricCharacteristicMatrix_det x _
    _ = Complex.I ^ 2 * (x : ℂ) ^ 2 + (x : ℂ) ^ 2 := by ring
    _ = 0 := by rw [Complex.I_sq]; ring

theorem negativeImaginaryEigenvalue_root (x : ℝ) :
    Polynomial.IsRoot (skewSymmetricCharacteristicPolynomial x)
      (-(Complex.I * (x : ℂ))) := by
  rw [Polynomial.IsRoot.def]
  calc
    (skewSymmetricCharacteristicPolynomial x).eval (-(Complex.I * (x : ℂ))) =
        (skewSymmetricCharacteristicMatrix x (-(Complex.I * (x : ℂ)))).det :=
      skewSymmetricCharacteristicPolynomial_eval x _
    _ = (-(Complex.I * (x : ℂ))) ^ 2 + (x : ℂ) ^ 2 :=
      skewSymmetricCharacteristicMatrix_det x _
    _ = Complex.I ^ 2 * (x : ℂ) ^ 2 + (x : ℂ) ^ 2 := by ring
    _ = 0 := by rw [Complex.I_sq]; ring

theorem positiveImaginaryEigenvector_nonzero :
    (![(1 : ℂ), Complex.I] : Fin 2 → ℂ) ≠ 0 := by
  intro h
  have h0 : (1 : ℂ) = 0 := by
    simpa using congrFun h (0 : Fin 2)
  norm_num at h0

theorem negativeImaginaryEigenvector_nonzero :
    (![(1 : ℂ), -Complex.I] : Fin 2 → ℂ) ≠ 0 := by
  intro h
  have h0 : (1 : ℂ) = 0 := by
    simpa using congrFun h (0 : Fin 2)
  norm_num at h0

theorem skewSymmetricMatrix_mulVec_positive (x : ℝ) :
    skewSymmetricMatrix x *ᵥ ![(1 : ℂ), Complex.I] =
      (Complex.I * (x : ℂ)) • ![(1 : ℂ), Complex.I] := by
  ext i
  fin_cases i <;>
    simp [skewSymmetricMatrix, Matrix.mulVec, Fin.sum_univ_two] <;>
    ring_nf <;>
    rw [Complex.I_sq] <;>
    ring

theorem skewSymmetricMatrix_mulVec_negative (x : ℝ) :
    skewSymmetricMatrix x *ᵥ ![(1 : ℂ), -Complex.I] =
      (-(Complex.I * (x : ℂ))) • ![(1 : ℂ), -Complex.I] := by
  ext i
  fin_cases i <;>
    simp [skewSymmetricMatrix, Matrix.mulVec, Fin.sum_univ_two] <;>
    ring_nf <;>
    rw [Complex.I_sq] <;>
    ring

theorem skewSymmetricMatrix_hasPositiveEigenvector (x : ℝ) :
    Module.End.HasEigenvector (skewSymmetricMatrix x).toLin'
      (Complex.I * (x : ℂ)) ![(1 : ℂ), Complex.I] := by
  refine (Module.End.hasEigenvector_iff).2 ⟨?_, positiveImaginaryEigenvector_nonzero⟩
  refine (Module.End.mem_eigenspace_iff).2 ?_
  simpa only [Matrix.toLin'_apply] using skewSymmetricMatrix_mulVec_positive x

theorem skewSymmetricMatrix_hasNegativeEigenvector (x : ℝ) :
    Module.End.HasEigenvector (skewSymmetricMatrix x).toLin'
      (-(Complex.I * (x : ℂ))) ![(1 : ℂ), -Complex.I] := by
  refine (Module.End.hasEigenvector_iff).2 ⟨?_, negativeImaginaryEigenvector_nonzero⟩
  refine (Module.End.mem_eigenspace_iff).2 ?_
  simpa only [Matrix.toLin'_apply] using skewSymmetricMatrix_mulVec_negative x

theorem skewSymmetricMatrix_hasPositiveEigenvalue (x : ℝ) :
    Module.End.HasEigenvalue (skewSymmetricMatrix x).toLin'
      (Complex.I * (x : ℂ)) :=
  Module.End.hasEigenvalue_of_hasEigenvector
    (skewSymmetricMatrix_hasPositiveEigenvector x)

theorem skewSymmetricMatrix_hasNegativeEigenvalue (x : ℝ) :
    Module.End.HasEigenvalue (skewSymmetricMatrix x).toLin'
      (-(Complex.I * (x : ℂ))) :=
  Module.End.hasEigenvalue_of_hasEigenvector
    (skewSymmetricMatrix_hasNegativeEigenvector x)

theorem measurable_pos_imaginary_eigenvalue
    {Ω : Type*} [MeasurableSpace Ω] {X : Ω → ℝ}
    (hX : Measurable X) :
    IsComplexRandomVariable (fun omega => Complex.I * (X omega : ℂ)) := by
  have hXc : Measurable (fun omega => (X omega : ℂ)) :=
    Complex.measurable_ofReal.comp hX
  simpa [IsComplexRandomVariable] using hXc.const_mul Complex.I

theorem measurable_neg_imaginary_eigenvalue
    {Ω : Type*} [MeasurableSpace Ω] {X : Ω → ℝ}
    (hX : Measurable X) :
    IsComplexRandomVariable (fun omega => -Complex.I * (X omega : ℂ)) := by
  have hXc : Measurable (fun omega => (X omega : ℂ)) :=
    Complex.measurable_ofReal.comp hX
  simpa [IsComplexRandomVariable] using hXc.const_mul (-Complex.I)

theorem ex_4_4_2
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ)
    (hX : Measurable X)
    (hGaussian : ProbabilityTheory.HasLaw X
      (ProbabilityTheory.gaussianReal 0 (1 : NNReal)) P) :
    (∀ omega, (skewSymmetricMatrix (X omega)).transpose =
      -skewSymmetricMatrix (X omega)) ∧
    (∀ omega lam, (skewSymmetricCharacteristicMatrix (X omega) lam).det =
      lam ^ 2 + (X omega : ℂ) ^ 2) ∧
    (∀ omega, Polynomial.IsRoot (skewSymmetricCharacteristicPolynomial (X omega))
      (Complex.I * (X omega : ℂ))) ∧
    (∀ omega, Polynomial.IsRoot (skewSymmetricCharacteristicPolynomial (X omega))
      (-(Complex.I * (X omega : ℂ)))) ∧
    (∀ omega, Module.End.HasEigenvalue (skewSymmetricMatrix (X omega)).toLin'
      (Complex.I * (X omega : ℂ))) ∧
    (∀ omega, Module.End.HasEigenvalue (skewSymmetricMatrix (X omega)).toLin'
      (-(Complex.I * (X omega : ℂ)))) ∧
    IsComplexRandomVariable (fun omega => Complex.I * (X omega : ℂ)) ∧
    IsComplexRandomVariable (fun omega => -Complex.I * (X omega : ℂ)) := by
  exact ⟨
    fun omega => skewSymmetricMatrix_transpose (X omega),
    fun omega lam => skewSymmetricCharacteristicMatrix_det (X omega) lam,
    fun omega => positiveImaginaryEigenvalue_root (X omega),
    fun omega => negativeImaginaryEigenvalue_root (X omega),
    fun omega => skewSymmetricMatrix_hasPositiveEigenvalue (X omega),
    fun omega => skewSymmetricMatrix_hasNegativeEigenvalue (X omega),
    measurable_pos_imaginary_eigenvalue hX,
    measurable_neg_imaginary_eigenvalue hX⟩
