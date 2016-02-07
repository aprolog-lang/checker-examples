exp : type.
id  : name_type.
ty  : type.
ctx : type.

u   : exp.
var : id -> exp.
app : (exp,exp) -> exp.
lam : id\exp -> exp.
pair: (exp,exp) -> exp.
fst : exp -> exp.
snd : exp -> exp.

unitTy : ty.
funTy  : (ty,ty) -> ty.
pairTy : (ty,ty) -> ty.

type ctx = [(id,ty)].


