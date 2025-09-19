module Surface : sig
  type producer
  type consumer
  type cut
  type t = cut

  module Show : sig
      val show : t -> string
  end
  
  val variable : string -> producer
  val covariable : string -> consumer
  val mu : string -> cut -> producer
  val mutilde : string -> cut -> consumer
  val cut : producer -> consumer -> cut
end