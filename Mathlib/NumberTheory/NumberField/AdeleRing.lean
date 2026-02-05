/-
Copyright (c) 2024 Salvatore Mercuri, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri, María Inés de Frutos-Fernández
-/
module

public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.ProductFormula
public import Mathlib.Algebra.Group.Pi.Units

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

def IdeleGroup (R K : Type) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] : Type := (AdeleRing R K)ˣ

section norm

variable {K : Type*} [Field K] [NumberField K]

namespace FiniteAdeleRing

open RingOfIntegers.HeightOneSpectrum

-- not true! the product formula is meant to be for the ideles
theorem mulSupport_finite {x : (FiniteAdeleRing (𝓞 K) K)ˣ} :
    (Function.mulSupport fun v ↦ ‖x.1 v‖).Finite := by
  have := FiniteAdeleRing.isUnit_iff.1 x.isUnit
  obtain h := this.2
  simp at h
  simp [instNormedFieldValuedAdicCompletion, Valued.toNormedField]
  simp_rw [Valued.norm_def]
  change (Function.mulSupport fun v ↦ (WithZeroMulInt.toNNReal (absNorm_ne_zero v) (Valued.v (x.1 v)) : ℝ)).Finite
  convert h
  ext v
  simp
  apply Iff.not
  constructor
  · intro h
    rw [map_eq_one_iff] at h
    exact h
    exact WithZeroMulInt.toNNReal_strictMono (one_lt_absNorm_nnreal v) |>.injective
  · rintro h
    simp_rw [h]
    simp

-- not realy defined outside the units, gets junk value of 1
instance : Norm (FiniteAdeleRing (𝓞 K) K)ˣ where norm x := ∏ᶠ v, ‖x.1 v‖

theorem norm_def (x : (FiniteAdeleRing (𝓞 K) K)ˣ) : ‖x‖ = ∏ᶠ v, ‖x.1 v‖ := rfl

theorem coe_norm_apply (x : Kˣ) :
    ‖(x : (FiniteAdeleRing (𝓞 K) K)ˣ)‖ = ∏ᶠ v, FinitePlace.mk v x.1 := rfl

theorem coe_norm_apply_eq_finprod_finitePlace (x : Kˣ) :
    ‖(x : (FiniteAdeleRing (𝓞 K) K)ˣ)‖ = ∏ᶠ v : FinitePlace K, v x := by
  rw [coe_norm_apply, ← finprod_comp FinitePlace.equivHeightOneSpectrum.invFun
    FinitePlace.equivHeightOneSpectrum.symm.bijective]
  exact finprod_congr fun _ ↦ rfl

theorem coe_norm_eq_inv_abs_norm (x : Kˣ) :
    ‖(x : (FiniteAdeleRing (𝓞 K) K)ˣ)‖ = |Algebra.norm ℚ x.1|⁻¹ := by
  rw [← FinitePlace.prod_eq_inv_abs_norm x.ne_zero, coe_norm_apply_eq_finprod_finitePlace]

end FiniteAdeleRing

namespace AdeleRing

theorem isUnit_iff {x : AdeleRing (𝓞 K) K} :
    IsUnit x ↔ (∀ v, x.1 v ≠ 0) ∧ (∀ v, x.2 v ≠ 0) ∧
      ∀ᶠ v in Filter.cofinite, Valued.v (x.2 v) = 1 := by
  rw [Prod.isUnit_iff, Pi.isUnit_iff, FiniteAdeleRing.isUnit_iff]
  simp_rw [isUnit_iff_ne_zero]

instance : Norm (AdeleRing (𝓞 K) K)ˣ where norm x := ‖x.1.1‖ * ‖(MulEquiv.prodUnits x).2‖

theorem norm_def (x : (AdeleRing (𝓞 K) K)ˣ) : ‖x‖ = ‖x.1.1‖ * ‖(MulEquiv.prodUnits x).2‖ := rfl

theorem norm_apply (x : (AdeleRing (𝓞 K) K)ˣ) :
    ‖x‖ = (∏ v, ‖x.1.1 v‖ ^ v.mult) * ∏ᶠ v, ‖(MulEquiv.prodUnits x).2.1 v‖ := rfl

variable (K) in
def unitEmbedding : Kˣ →* (AdeleRing (𝓞 K) K)ˣ := Units.map (algebraMap K (AdeleRing (𝓞 K) K))

@[simp] theorem unitEmbedding_apply (k : Kˣ) :
    unitEmbedding K k = algebraMap K (AdeleRing (𝓞 K) K) k := rfl

theorem unitEmbedding_prodUnits_apply (k : Kˣ) :
    (MulEquiv.prodUnits (unitEmbedding K k)).2 = k := rfl

instance : Coe Kˣ (AdeleRing (𝓞 K) K)ˣ where
  coe x := unitEmbedding K x

theorem coe_norm_eq_one {x : Kˣ} :
    ‖(x : (AdeleRing (𝓞 K) K)ˣ)‖ = 1 := by
  rw [norm_def, unitEmbedding_apply, algebraMap_fst_def]
  rw [unitEmbedding_prodUnits_apply, InfiniteAdeleRing.coe_norm_eq_abs_norm,
    FiniteAdeleRing.coe_norm_eq_inv_abs_norm x]
  simp

end AdeleRing

end norm

end NumberField
