open Core

open Examplecoq

module NetworkBuffer = AbstractNetworkBuffer(struct
type coq_Data = string

let coq_Data_eqMixin = Equality.{op=String.(=); mixin_of__1=()}
end)

