

module monad

// Identity Monad
let pureID x = x
let bindID x my = my x

// Option Monad
let pureOption x = Some x
let bindOption x y =
  match x with
    | Some u -> y u
    | None   -> None

// Reader Monad Transformer
let runReaderT r m = m r

let pureReaderT p x = fun _ -> p x
let bindReaderT b x y = fun r -> runReaderT r x |>
                                 b <| (y >> runReaderT r)

let readT p = p
let liftReaderT m = fun _ -> m


// State Monad Transformer
let runStateT s m = m s

let pureStateT p x = fun s -> p (x,s)
let bindStateT b x y = fun s -> b (x s) (fun (x',s') -> y x' s')

let getT p = fun s -> p (s,s)
let putT p s = fun _ -> p ((),s)

(* For an example usage see the W Monad in the file core.fs *)
