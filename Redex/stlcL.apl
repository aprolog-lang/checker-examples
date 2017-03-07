exp : type.
id  : name_type.
ty  : type.
cnt : type.


% u   : exp.
c   : cnt -> exp.
var : id -> exp.
app : (exp,exp) -> exp. %% use infix?
lam : (id\exp,ty) -> exp.
error : exp.

% constants
cons : cnt.
hd : cnt.
tl : cnt.
nil : cnt.
toInt : int -> cnt.
%% plus : cnt.

% unitTy : ty.
intTy : ty.
funTy  : (ty,ty) -> ty.
%% changed this to make in constant as in redex
listTy :  ty.


type ctx = [(id,ty)].

% int added
% remove u ?
