/-
Copyright (c) 2024 Salvatore Mercuri, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri, María Inés de Frutos-Fernández
-/
module

public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.ProductFormula

/-!
# The adele ring of a number field

This file contains the formalisation of the adele ring of a number field as the
direct product of the infinite adele ring and the finite adele ring.

## Main definitions

- `NumberField.AdeleRing K` is the adele ring of a number field `K`.
- `NumberField.AdeleRing.principalSubgroup K` is the subgroup of principal adeles `(x)ᵥ`.

## References
* [J.W.S. Cassels, A. Fröhlich, *Algebraic Number Theory*][cassels1967algebraic]

## Tags
adele ring, number field
-/

@[expose] public section

noncomputable section

namespace NumberField

open InfinitePlace AbsoluteValue.Completion InfinitePlace.Completion IsDedekindDomain

/-! ## The adele ring  -/

/-- `AdeleRing (𝓞 K) K` is the adele ring of a number field `K`.

More generally `AdeleRing R K` can be used if `K` is the field of fractions
of the Dedekind domain `R`. This enables use of rings like `AdeleRing ℤ ℚ`, which
in practice are easier to work with than `AdeleRing (𝓞 ℚ) ℚ`.

Note that this definition does not give the correct answer in the function field case.
-/
def AdeleRing (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] := InfiniteAdeleRing K × FiniteAdeleRing R K

namespace AdeleRing

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]

instance : CommRing (AdeleRing R K) := Prod.instCommRing

instance : Inhabited (AdeleRing R K) := ⟨0⟩

instance : TopologicalSpace (AdeleRing R K) := instTopologicalSpaceProd

instance : IsTopologicalRing (AdeleRing R K) := instIsTopologicalRingProd

instance : Algebra K (AdeleRing R K) := Prod.algebra _ _ _

@[simp]
theorem algebraMap_fst_apply (x : K) (v : InfinitePlace K) :
    (algebraMap K (AdeleRing R K) x).1 v = x := rfl

theorem algebraMap_fst_def (x : K) :
    (algebraMap K (AdeleRing R K) x).1 = algebraMap K (InfiniteAdeleRing K) x := rfl

@[simp]
theorem algebraMap_snd_apply (x : K) (v : HeightOneSpectrum R) :
    (algebraMap K (AdeleRing R K) x).2 v = x := rfl

theorem algebraMap_snd_def (x : K) :
    (algebraMap K (AdeleRing R K) x).2 = algebraMap K (FiniteAdeleRing R K) x := rfl

theorem algebraMap_injective [NumberField K] : Function.Injective (algebraMap K (AdeleRing R K)) :=
  fun _ _ hxy => (algebraMap K _).injective (Prod.ext_iff.1 hxy).1

/-- The subgroup of principal adeles `(x)ᵥ` where `x ∈ K`. -/
abbrev principalSubgroup : AddSubgroup (AdeleRing R K) := (algebraMap K _).range.toAddSubgroup

end AdeleRing

section norm

variable {K : Type*} [Field K] [NumberField K]

namespace FiniteAdeleRing

instance : Norm (FiniteAdeleRing (𝓞 K) K) where
  norm x := ∏ᶠ v, ‖x v‖

theorem norm_apply (x : FiniteAdeleRing (𝓞 K) K) : ‖x‖ = ∏ᶠ v, ‖x v‖ := rfl

theorem coe_norm_apply (x : K) :
    ‖algebraMap _ (FiniteAdeleRing (𝓞 K) K) x‖ = ∏ᶠ v, FinitePlace.mk v x := rfl

theorem coe_norm_apply_eq_finprod_finitePlace (x : K) :
    ‖algebraMap _ (FiniteAdeleRing (𝓞 K) K) x‖ = ∏ᶠ v : FinitePlace K, v x := by
  rw [coe_norm_apply, ← finprod_comp FinitePlace.equivHeightOneSpectrum.invFun
    FinitePlace.equivHeightOneSpectrum.symm.bijective]
  exact finprod_congr fun _ ↦ rfl

theorem coe_norm_eq_inv_abs_norm {x : K} (hx : x ≠ 0) :
    ‖algebraMap _ (FiniteAdeleRing (𝓞 K) K) x‖ = |Algebra.norm ℚ x|⁻¹ := by
  rw [← FinitePlace.prod_eq_inv_abs_norm hx, coe_norm_apply_eq_finprod_finitePlace]

end FiniteAdeleRing

namespace AdeleRing

instance : Norm (AdeleRing (𝓞 K) K) where norm x := ‖x.1‖ * ‖x.2‖

theorem norm_def (x : AdeleRing (𝓞 K) K) : ‖x‖ = ‖x.1‖ * ‖x.2‖ := rfl

theorem norm_apply (x : AdeleRing (𝓞 K) K) : ‖x‖ = (∏ v, ‖x.1 v‖ ^ v.mult) * ∏ᶠ v, ‖x.2 v‖ := rfl

theorem coe_norm_eq_one {x : K} (hx : x ≠ 0) :
    ‖algebraMap _ (AdeleRing (𝓞 K) K) x‖ = 1 := by
  simp [norm_def, algebraMap_fst_def, InfiniteAdeleRing.norm_apply, algebraMap_snd_def,
    FiniteAdeleRing.coe_norm_apply_eq_finprod_finitePlace]
  rw [← prod_abs_eq_one hx]
  rfl

end AdeleRing

end norm

end NumberField
