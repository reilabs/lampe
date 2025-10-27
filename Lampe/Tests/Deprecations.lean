import Lampe

open Lampe

[[deprecated]]
noir_def my_func1<>() -> Unit := {
  #_unit
}

/--
warning: `my_func1` has been deprecated:
-/
#guard_msgs in
def my_func1_deprecated := my_func1

[[deprecated "Use XXX instead"]]
noir_def my_func2<>() -> Unit := {
  #_unit
}

/--
warning: `my_func2` has been deprecated: Use XXX instead
-/
#guard_msgs in
def my_func2_deprecated := my_func2

[[deprecated "Use XXX instead"]]
noir_struct_def FooStruct<I: Type> {
  I,
  I
}

/--
warning: `FooStruct` has been deprecated: Use XXX instead
-/
#guard_msgs in
def FooStruct_deprecated := FooStruct

