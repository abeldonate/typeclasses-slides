import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Constructions.SumProd
import Mathlib

-- Assume X and Y are MetricSpaces
variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

set_option trace.Meta.synthInstance true
example : TopologicalSpace X := inferInstance

-- set_option trace.Meta.synthInstance.resume true
example : TopologicalSpace X := inferInstance

example : MetricSpace (X × Y) := inferInstance

example : TopologicalSpace (X × Y) := inferInstance


variable {G : Type*} [CommGroup G]

example : Group G := inferInstance
