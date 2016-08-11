# * Copyright 2015, NICTA
# *
# * This software may be distributed and modified according to the terms of
# * the BSD 2-Clause license. Note that NO WARRANTY is provided.
# * See "LICENSE_BSD2.txt" for details.
# *
# * @TAG(NICTA_BSD)

# Syntax and simple operations for types, expressions, graph nodes
# and graph functions (functions in graph-language format).

from target_objects import structs, trace
import target_objects

quick_reference = """
Quick reference on the graph language and its syntax.
=====================================================

Example
=======

Let's build up the syntax that roughly mirrors the C statement x = y + 1;

This is a quick example. A more thorough reference is below.

We have two example types: Bool and Word 32.

Here are two atomic expressions of type Word 32:
Var y Word 32
Num 1 Word 32

These encode the variable y and the number 1, both of type Word 32.

Expressions in this language are built up by concatenating strings of tokens.
Any whitespace delimited string can be a token, and thus a variable name.

Compound expressions are built with operators, e.g. y + 1:
Op Plus Word 32 2 Var y Word 32 Num 1 Word 32

This is quite verbose. For simplicity, the Op syntax includes the type of
the whole expression - Word 32 - and the number of arguments - 2 - even though
much of this information is redundant.

Finally, we can encode the statement x = y + 1; at address 14.

14 Basic 15 1 x Word 32 Op Plus Word 32 2 Var y Word 32 Num 1 Word 32

This specifies that node 14 is a basic node (which updates variables). The
successor node is 15. It updates 1 variable (basic nodes may simultaneously
update many variables). The variable to be updated is specified by x Word 32.
The remainder of the line is the expression y + 1 as seen before.

We can encode the statements if (x == z) { return; } as follows:
15 Cond 16 17 Op Equals Bool Var x Word 32 Var y Word 32
16 Basic Ret 0

Conditional node 15 continues to node 16 if x == y, and to 17 otherwise. Node
16 is a basic node which updates no variables, i.e. a skip statement. It
continues to the special address Ret which designates return from the current
function.

Reference
=========

A graph program consists of a number of functions, each
of whose control flow is structured as a graph of nodes
with integer addresses. Nodes are of three types:
  - 'Basic' updates variable values.
  - 'Cond' chooses between two successor nodes.
  - 'Call' makes calls to functions.

A top level syntax file (interpreted by syntax.parse_all)
contains two kinds of sections:
  - Function blocks introduce functions.
  - Struct blocks introduce aggregate types (e.g. struct in C).

All lines in the input syntax are read as a whitespace-separated
list of tokens. Empty lines and lines whose first non-whitespace
character is '#' are ignored. All syntax is prefix encoded, so
each clause has a first token which determines what kind of clause
it is, followed by the concatenation of all of its subclauses.

The two kinds of lines that appear in Struct blocks illustrate this format:
Struct "struct name" <int size> <int alignment>
StructField "name" <type> <int offset>

On notation: above we denote the specific tokens 'Struct' and 'StructField',
the arbitrary tokens "name" etc, the special integer subclauses <int size> etc,
and a <type> subclause. Integer subclauses always consist of a single token.
A leading character '-' or '~' indicates negative. A leading '0x' or '0b'
indicates hexadecimal or binary encoding, otherwise decimal, e.g. 1, 0x1A,
-0x2b, ~0b1100, etc. Naming tokens can be anything at all that does not contain
whitespace, so x y'v a,b c#d # etc are all valid struct or field names.

Struct blocks begin with the 'Struct' line, which specifies their name, total
size and required alignment. The struct block then contains a number of
StructField lines, where each field has a type and an offset from the start of
the structure. The Struct block ends where any other Struct or Function block
begins.

Function blocks begin with a function declaration line
  Function "name of function" <int>*("input argument name" <type>)
    <int>*("output argument name" <type>)

The notation <int>*(...) above denotes an arbitrary length list of subclauses.
The first token of this clause will be a decimal integer specifying the length
of the list. For instance, the classic 'XOR' function with inputs x, y and
output z could be specified as follows:
Function XOR 2 x Bool y Bool 1 z Bool

Each function has a name, a list of input arguments, and a list of output
arguments. The state in the graph language is entirely encoded in variables,
so functions will typically have global objects such as the heap as both input
and output arguments.

The function block may end immediately, for functions with unspecified body,
or may contain a number of graph node lines, followed by an entry point line:
EntryPoint <int>
The entry point line ends the function block.

A graph node line has one of these formats:
<int> Basic <next node> <int>*("var name" <type> <expression>)
<int> Cond <next node> <next node> <expression>
<int> Call <next node> "fun name" <int>*(<expression>) <int>*("var name" <type>)

Each node line begins with an integer which is the address of the node. A
<next node> is either the integer address of the following node, or one of the
special address tokens Ret and Err.

Basic nodes update the value of a (possibly empty) list of variables. The
variables are all updated simultaneously to the computed value of the
expressions given.

Cond nodes evaluate an expresion which must be of boolean type. They specify
two possible next nodes, left and right. The left node is visited when the
expression evaluates to true, the right on false.

Call nodes call another function of a given name. The list of arguments
expressions is evaluated and must match the list of input arguments of the
given function (same length and types). These arguments define the starting
variable environment of that function. Its return parameters are saved to the
list of variables given.

The <type> clauses are in one of these formats:
Word <int>  -- BitVec <int> is a synonym
Array <type> <int>
Struct "struct name"
Ptr <type>
One of the builtin types as a single token:
  'Bool Mem Dom HTD PMS UNIT Type Token RoundingMode'
FloatingPoint <int> <int>

These types encode a machine word with the given number of bits, an array of
some type, a struct previously defined by a Struct clause, or a pointer to
another type. The Array, Struct and Ptr types are provided only for use in
pointer validity assertions, which are discussed below. The FloatingPoint type
exactly mirrors the SMTLIB2 (_ FloatingPoint eb sb) type, and is available as
an optional extension. Using the FloatingPoint and RoundingMode types in any
problem changes the SMT theory needed and may limit which solvers and features
can be used.

Of the builtin types, booleans are standard, UNIT is the singleton type, and
memory is a 32-bit to 8-bit mapping. We aim to include 64-bit support soon. The
Dom type is a set of 32-bit values, used to encode the valid domain of memory
operations. The heap type description HTD is used by pointer-validity
operators. The phantom machine state type PMS is unspecified and used to
represent unspecified aspects of the environment. The type Type is the type of
Type expressions which are used in pointer-validity. 

The <expression> clauses have one of these formats:
Var "name" <type>
Op "name" <type> <int>*(<expression>)
Num <int> <type>
Type <type>
Symbol "name" <type>

Most of the expressions of the language are composed from variables, numerals
and operator applications, which should be self explanatory. The Type
expression wraps a type into an expression (of type Type) so it may be passed
to a pointer-validity operator.

The special Symbol clauses are used to denote in source languages the values
symbols will have in the binaries. They are replaced by specific numerals in
a first pass.

Many of the builtin operators are equivalent to SMTLIB2 operators, and are also
available with their SMTLIB2 names. The operators are:
  - Binary arithmetic operators on words:
    + Plus/bvadd, Minus/bvsub, Times/bvmul, Modulus/bvurem, DividedBy/bvudiv,
      BWAnd/bvand, BWOr/bvor, BWXOR/bvxor,
      ShiftLeft/bvshl, ShiftRight/bvlshr, SignedShiftRight/bvashr
  - Binary operators on booleans:
    + And/and, Or/or, Implies
  - Unary operators on bools:
    + Not/not
  - Booleans (nullary operators, i.e. constants):
    + True/true, False/false
  - Equals relation in any type:
    + Equals
  - Comparison relations on words (result is bool):
    + Less/bvult, LessEquals/bvule, SignedLess/bvslt, SignedLessEquals/bvsle
  - Unary operators on words:
    + BWNot/bvnot, CountLeadingZeroes
  - Cast operators on words - result type may be different to argument type:
    + WordCast, WordCastSigned
  - Memory operations:
    + MemAcc (args [m :: Mem, ptr :: Word 32]) any word type
    + MemUpdate (args, [m :: Mem, ptr :: Word 32, v :: any word type])
  - Pointer-validity operators:
    + PValid, PWeakValid, PAlignValid, PGlobalValid, PArrayValid
  - Miscellaneous:
    + MemDom, HTDUpdate
    + IfThenElse/ite (args [b :: bool, x :: any type T, y :: T])
  - FloatingPoint operations from the SMTLIB2 floating point specification:
    + roundNearestTiesToEven/RNE, roundNearestTiesToAway/RNA,
      roundTowardPositive/RTP, roundTowardNegative/RTN,
      roundTowardZero/RTZ
    + fp.abs, fp.neg, fp.add, fp.sub, fp.mul, fp.div, fp.fma, fp.sqrt,
      fp.rem, fp.roundToIntegral, fp.min, fp.max, fp.leq, fp.lt,
      fp.geq, fp.gt, fp.eq, fp.isNormal, fp.IsSubnormal, fp.isZero,
      fp.isInfinite, fp.isNaN, fp.isNegative, fp.isPositive
    + ToFloatingPoint, ToFloatingPointSigned, ToFloatingPointUnsigned,
      FloatingPointCast

Operators with SMTLIB2 equivalents have the same semantics. Mem and Dom
operations are wrap the SMTLIB2 BitVec Array type with more convenient
operations.

Memory accesses and updates can operate on various word types.

The pointer-validity operators PValid, PWeakValid, PGlobalValid all take 3
arguments of type HTD, Type, and Word 32. The PValid operator asserts that
the heap-type-description contains this type starting at this address. This
is exclusive with any incompatible type. PGlobalValid additionally asserts that
this is a global object, and therefore not contained within any larger object.
PWeakValid asserts that the type could be valid (it is aligned and within the
range of available addresses in the heap-type-description) and is needed only
in rare circumstances. PAlignValid omits the HTD argument and asserts only that
the pointer is appropriately aligned and that the object does not start at or
wrap around the 0 address. PArrayValid takes an additional argument (HTD,
Type, Word 32, Word 32) where the final argument specifies the number of
entries in an array.

The MemDom operator takes argument types [Word 32, Dom] and returns the boolean
of whether this pointer is in this domain.

The IfThenElse operator takes a bool and any two arguments of the same type.

The FloatingPoint operators are mostly taken from the SMTLIB2 floating
point standard. The conversions ToFloatingPoint ([Word] to FP),
ToFloatingPointSigned and ToFloatingPointUnsigned ([RoundingMode, Word] to FP)
and FloatingPointCast (FP to FP) represent the variants of to_fp in the SMTLIB2
standard.
"""

class Type:
	def __init__ (self, kind, name, el_typ=None):
		self.kind = kind
		if kind in ['Array', 'Word', 'TokenWords']:
			self.num = int (name)
		else:
			self.name = name
		if kind in ['Array', 'Ptr']:
			self.el_typ_symb = el_typ
			self.el_typ = concrete_type (el_typ)
		if kind in ['WordArray', 'FloatingPoint']:
			self.nums = [int (name), int (el_typ)]
	
	def __repr__ (self):
		if self.kind == 'Array':
			return 'Type ("Array", %r, %r)' % (self.num,
				self.el_typ_symb)
		elif self.kind in ('Word', 'TokenWords'):
			return 'Type (%r, %r)' % (self.kind, self.num)
		elif self.kind == 'Ptr':
			return 'Type ("Ptr", %r)' % self.el_typ_symb
		elif self.kind in ('WordArray', 'FloatingPoint'):
			return 'Type (%r, %r, %r)' % tuple ([self.kind]
				+ self.nums)
		else:
			return 'Type (%r, %r)' % (self.kind, self.name)

	def __eq__ (self, other):
		if not other:
			return False
		if self.kind != other.kind:
			return False
		if self.kind in ['Array', 'Word', 'TokenWords']:
			if self.num != other.num:
				return False
		elif self.kind in ['WordArray', 'FloatingPoint']:
			if self.nums != other.nums:
				return False
		else:
			if self.name != other.name:
				return False
		if self.kind in ['Array', 'Ptr']:
			if self.el_typ_symb != other.el_typ_symb:
				return False
		return True

	def __ne__ (self, other):
		return not other or not (self == other)

	def __hash__ (self):
		return hash(str(self))

	def __cmp__ (self, other):
		self_ss = []
		self.serialise (self_ss)
		other_ss = []
		other.serialise (other_ss)
		return cmp (self_ss, other_ss)

	def subtypes (self):
		if self.kind == 'Struct':
			return structs[self.name].subtypes()
		elif self.kind == 'Array':
			return [self] + self.el_typ.subtypes()
		else:
			return [self]

	def size (self):
		if self.kind == 'Struct':
			return structs[self.name].size
		elif self.kind == 'Array':
			return self.el_typ.size() * self.num
		elif self.kind == 'Word':
			assert self.num % 8 == 0, self
			return self.num / 8
		elif self.kind == 'FloatingPoint':
			sz = sum (self.nums)
			assert sz % 8 == 0, self
			return sz / 8
		elif self.kind == 'Ptr':
			return 4
		else:
			assert not 'type has size'

	def align (self):
		if self.kind == 'Struct':
			return structs[self.name].align
		elif self.kind == 'Array':
			return self.el_typ.align ()
		elif self.kind in ('Word', 'FloatingPoint'):
			return self.size ()
		elif self.kind == 'Ptr':
			return 4
		else:
			assert not 'type has alignment'

	def serialise (self, xs):
		if self.kind in ('Word', 'TokenWords'):
			xs.append (self.kind)
			xs.append (str (self.num))
		elif self.kind in ('WordArray', 'FloatingPoint'):
			xs.append (self.kind)
			xs.extend ([str (n) for n in self.nums])
		elif self.kind == 'Builtin':
			xs.append (self.name)
		elif self.kind == 'Array':
			xs.append ('Array')
			self.el_typ_symb.serialise (xs)
			xs.append (str (self.num))
		elif self.kind == 'Struct':
			xs.append ('Struct')
			xs.append (self.name)
		elif self.kind == 'Ptr':
			xs.append ('Ptr')
			self.el_typ_symb.serialise (xs)
		else:
			assert not 'type serialisable', self.kind

class Expr:
	def __init__ (self, kind, typ, name = None, struct = None,
			field = None, val = None, vals = None):
		self.kind = kind
		self.typ = typ
		if name != None:
			self.name = name
		if struct != None:
			self.struct = struct
		if field != None:
			self.field = field
		if val != None:
			self.val = val
		if vals != None:
			self.vals = vals
		if kind == 'Op':
			assert type (self.vals) == list

	def binds (self):
		binds = []
		if self.kind in set (['Symbol', 'Var', 'ConstGlobal', 'Token']):
			binds.append(('name', self.name))
		elif self.kind in ['Array', 'StructCons']:
			binds.append(('vals', self.vals))
		elif self.kind == 'Field':
			binds.append(('struct', self.struct))
			binds.append(('field', self.field))
		elif self.kind == 'FieldUpd':
			binds.append(('struct', self.struct))
			binds.append(('field', self.field))
			binds.append(('val', self.val))
		elif self.kind == 'Num':
			binds.append(('val', self.val))
		elif self.kind == 'Op':
			binds.append(('name', self.name))
			binds.append(('vals', self.vals))
		elif self.kind == 'Type':
			binds.append(('val', self.val))
		elif self.kind == 'SMTExpr':
			binds.append(('val', self.val))
		else:
			assert not 'expression understood for repr', self.kind
		return binds
 
	def __repr__ (self):
		bits = [repr(self.kind), repr(self.typ)]
		bits.extend(['%s = %r' % b for b in self.binds()])
		return 'Expr (%s)' % ', '.join(bits)

	def __eq__ (self, other):
		return (other and self.kind == other.kind
			and self.typ == other.typ
			and self.binds() == other.binds())

	def __ne__ (self, other):
		return not other or not (self == other)

	def __hash__ (self):
		return hash_tuplify (self.kind, self.typ, self.binds ())

	def __cmp__ (self, other):
		return cmp ((self.kind, self.typ, self.binds ()),
			(other.kind, other.typ, other.binds ()))

	def is_var (self, (nm, typ)):
		return self.kind == 'Var' and all([self.name == nm,
			self.typ == typ])

	def is_op (self, nm):
		if type (nm) == str:
			return self.kind == 'Op' and self.name == nm
		else:
			return self.kind == 'Op' and self.name in nm

	def visit (self, visit):
		visit (self)
		if self.kind == 'Var':
			pass
		elif self.kind == 'Op' or self.kind == 'Array':
			for x in self.vals:
				x.visit (visit)
		elif self.kind == 'StructCons':
			for x in self.vals.itervalues ():
				x.visit (visit)
		elif self.kind == 'Field':
			self.struct.visit (visit)

			struct_typ = self.struct.typ
			assert struct_typ.kind == 'Struct'
			struct = structs[struct_typ.name]
			(name, typ) = self.field
			assert struct.fields[name][0] == typ
		elif self.kind == 'FieldUpd':
			self.val.visit (visit)
			self.struct.visit (visit)

			struct_typ = self.struct.typ
			assert struct_typ.kind == 'Struct'
			struct = structs[struct_typ.name]
			(name, typ) = self.field
			assert struct.fields[name][0] == typ
		elif self.kind == 'ConstGlobal':
			assert (target_objects.const_globals[self.name].typ
				== self.typ)
		elif self.kind in set (['Num', 'Symbol', 'Type', 'Token']):
			pass
		else:
			assert not 'expr understood', self

	def gen_visit (self, visit_lval, visit_rval):
		self.visit (visit_rval)

	def subst (self, substor, ss = None):
		ret = False
		if self.kind == 'Op':
			subst_vals = subst_list (substor, self.vals)
			if subst_vals:
				self = Expr ('Op', self.typ, name = self.name,
					vals = subst_vals)
				ret = True
		if (ss == None or self.kind in ss or self.is_op (ss)):
			r = substor (self)
			if r != None:
				return r
		if ret:
			return self
		return

	def add_const_ranges (self, ranges):
		def visit (expr):
			if expr.kind == 'ConstGlobal':
				(start, size, _) = symbols[expr.name]
				assert size == expr.typ.size ()
				ranges[expr.name] = (start, start + size - 1)

		self.visit (visit)

	def get_mem_access (self):
		if self.is_op ('MemAcc'):
			[m, p] = self.vals
			return [('MemAcc', p, self, m)]
		elif self.is_op ('MemUpdate'):
			[m, p, v] = self.vals
			return [('MemUpdate', p, v, m)]
		else:
			return []

	def get_mem_accesses (self):
		accesses = []
		def visit (expr):
			accesses.extend (expr.get_mem_access ())
		self.visit (visit)
		return accesses

	def serialise (self, xs):
		xs.append (self.kind)
		if self.kind == 'Op':
			xs.append (self.name)
			self.typ.serialise (xs)
			xs.append (str (len (self.vals)))
			for v in self.vals:
				v.serialise (xs)
		elif self.kind == 'Num':
			xs.append (str (self.val))
			self.typ.serialise (xs)
		elif self.kind == 'Var':
			xs.append (self.name)
			self.typ.serialise (xs)
		elif self.kind == 'Type':
			self.val.serialise (xs)
		elif self.kind == 'Token':
			xs.extend ([self.kind, self.name])
			self.typ.serialise (xs)
		else:
			assert not 'expr serialisable', self.kind

class Struct:
	def __init__ (self, name, size, align):
		self.name = name
		self.size = size
		self.align = align
		self.field_list = []
		self.fields = {}
		self._subtypes = None
		self.typ = Type ('Struct', name)

	def add_field (self, name, typ, offset):
		concrete = concrete_type (typ)
		self.field_list.append ((name, concrete))
		self.fields[name] = (concrete, offset, typ)
		assert self._subtypes == None

	def subtypes (self):
		if self._subtypes != None:
			return self._subtypes
		xs = [self.typ]
		for (concrete, offs, typ2) in self.fields.itervalues():
			xs.extend(typ2.subtypes())
		self._subtypes = xs
		return xs

def tuplify (x):
	if type(x) == tuple or type(x) == list:
		return tuple ([tuplify (y) for y in x])
	if type(x) == dict:
		return tuple ([tuplify (y) for y in x.iteritems ()])
	else:
		return x

def hash_tuplify (* xs):
	return hash (tuplify (xs))

def subst_list (substor, xs, ss = None):
	ys = [x.subst (substor, ss = ss) for x in xs]
	if [y for y in ys if y != None]:
		xs = list (xs)
		for (i, y) in enumerate (ys):
			if y != None:
				xs[i] = y
		return xs
	else:
		return

class Node:
	def __init__ (self, kind, conts, args):
		self.kind = kind

		if type (conts) == list:
			if len (conts) == 1:
				the_cont = conts[0]
		else:
			the_cont = conts

		if kind == 'Basic':
			self.cont = the_cont
			self.upds = [(lv, v) for (lv, v) in args
				if not v.is_var (lv)]
		elif kind == 'Call':
			self.cont = the_cont
			(self.fname, self.args, self.rets) = args
		elif kind == 'Cond':
			(self.left, self.right) = conts
			self.cond = args
		else:
			assert not 'node kind understood', self.kind

	def __repr__ (self):
		return 'Node (%r, %r, %r)' % (self.kind,
			self.get_conts (), self.get_args ())

	def __hash__ (self):
		if self.kind == 'Call':
			return hash ((self.fname, tuple (self.args),
				tuple (self.rets), self.cont))
		elif self.kind == 'Basic':
			return hash (tuple (self.upds))
		elif self.kind == 'Cond':
			return hash ((self.cond, self.left, self.right))
		else:
			assert not 'node kind understood', self.kind

	def __eq__ (self, other):
		return all ([self.kind == other.kind,
			self.get_conts () == other.get_conts (),
			self.get_args () == other.get_args ()])

	def __ne__ (self, other):
		return not other or not self == other

	def get_args (self):
		if self.kind == 'Basic':
			return self.upds
		elif self.kind == 'Call':
			return (self.fname, self.args, self.rets)
		else:
			return self.cond

	def get_conts (self):
		if self.kind == 'Cond':
			return [self.left, self.right]
		else:
			return [self.cont]

	def get_lvals (self):
		if self.kind == 'Basic':
			return [lv for (lv, v) in self.upds]
		elif self.kind == 'Call':
			return self.rets
		else:
			return []

	def is_noop (self):
		if self.kind == 'Basic':
			return self.upds == []
		elif self.kind == 'Cond':
			return self.left == self.right
		else:
			return False

	def visit (self, visit_lval, visit_rval):
		if self.kind == 'Basic':
			for (lv, v) in self.upds:
				visit_lval (lv)
				v.visit (visit_rval)
		elif self.kind == 'Cond':
			self.cond.visit (visit_rval)
		elif self.kind == 'Call':
			for v in self.args:
				v.visit (visit_rval)
			for r in self.rets:
				visit_lval (r)

	def gen_visit (self, visit_lval, visit_rval):
		self.visit (visit_lval, visit_rval)

	def subst_exprs (self, substor, ss = None):
		if self.kind == 'Basic':
			rvs = subst_list (substor,
				[v for (lv, v) in self.upds], ss = ss)
			if rvs == None:
				return self
			return Node ('Basic', self.cont,
				zip ([lv for (lv, v) in self.upds], rvs))
		elif self.kind == 'Cond':
			r = self.cond.subst (substor, ss = ss)
			if r == None:
				return self
			return Node ('Cond', [self.left, self.right], r)
		elif self.kind == 'Call':
			args = subst_list (substor, self.args, ss = ss)
			if args == None:
				return self
			return Node ('Call', self.cont, (self.fname,
				args, self.rets))

	def get_mem_accesses (self):
		accesses = []
		def visit (expr):
			accesses.extend (expr.get_mem_access ())
		self.visit (lambda x: (), visit)
		return accesses

	def serialise (self, xs):
		xs.append (self.kind)
		xs.extend ([str (c) for c in self.get_conts ()])
		if self.kind == 'Basic':
			xs.append (str (len (self.upds)))
			for (lv, v) in self.upds:
				xs.append (lv[0])
				lv[1].serialise (xs)
				v.serialise (xs)
		elif self.kind == 'Cond':
			self.cond.serialise (xs)
		elif self.kind == 'Call':
			xs.append (self.fname)
			xs.append (str (len (self.args)))
			for arg in self.args:
				arg.serialise (xs)
			xs.append (str (len (self.rets)))
			for (nm, typ) in self.rets:
				xs.append (nm)
				typ.serialise (xs)

def rename_lval ((name, typ), renames):
	return (renames.get (name, name), typ)

def do_subst (expr, substor, ss = None):
	r = expr.subst (substor, ss = ss)
	if r == None:
		return expr
	else:
		return r

standard_expr_kinds = set (['Symbol', 'ConstGlobal', 'Var', 'Op', 'Num',
	'Type'])

def rename_expr_substor (renames):
	def ren (expr):
		if expr.kind == 'Var' and expr.name in renames:
			return mk_var (renames[expr.name], expr.typ)
		else:
			return
	return ren

def rename_expr (expr, renames):
	return do_subst (expr, rename_expr_substor (renames),
		ss = set (['Var']))

def copy_rename (node, renames):
	(vs, ns) = renames
	nf = lambda n: ns.get (n, n)
	node = node.subst_exprs (rename_expr_substor (vs))
	if node.kind == 'Call':
		return Node ('Call', nf (node.cont), (node.fname, node.args,
                              [rename_lval (l, vs) for l in node.rets]))
	elif node.kind == 'Basic':
		return Node ('Basic', nf (node.cont),
			[(rename_lval (lv, vs), v) for (lv, v) in node.upds])
	elif node.kind == 'Cond':
		return Node ('Cond', [nf (node.left), nf (node.right)],
			node.cond)
	else:
		assert not 'node kind understood', node.kind

class Function:
	def __init__ (self, name, inputs, outputs):
		self.name = name
		self.inputs = inputs
		self.outputs = outputs
		self.entry = None
		self.nodes = {}

	def __hash__ (self):
		en = self.entry
		if not en:
			en = -1
		return hash (tuple ([self.name, tuple (self.inputs),
				tuple (self.outputs), en])
			+ tuple (sorted (self.nodes.iteritems ())))

	def reachable_nodes (self, simplify = False):
		if not self.entry:
			return {}
		rs = {}
		vs = [self.entry]
		while vs:
			n = vs.pop()
			if type (n) == str:
				continue
			rs[n] = True
			node = self.nodes[n]
			if simplify:
				import logic
				node = logic.simplify_node_elementary (node)
			for c in node.get_conts ():
				if not c in rs:
					vs.append (c)
		return rs

	def serialise (self):
		xs = ['Function', self.name, str (len (self.inputs))]
		for (nm, typ) in self.inputs:
			xs.append (nm)
			typ.serialise (xs)
		xs.append (str (len (self.outputs)))
		for (nm, typ) in self.outputs:
			xs.append (nm)
			typ.serialise (xs)
		ss = [' '.join (xs)]
		if not self.entry:
			return ss
		for n in self.nodes:
			xs = [str (n)]
			self.nodes[n].serialise (xs)
			ss.append (' '.join (xs))
		ss.append ('EntryPoint %d' % self.entry)
		return ss

	def as_problem (self, Problem, name = 'temp'):
		p = Problem(None, 'Function (%s)' % self.name)
		p.clone_function (self, name)
		p.compute_preds ()
		return p

	def function_call_addrs (self):
		return [(n, self.nodes[n].fname)
			for n in self.nodes if self.nodes[n].kind == 'Call']

	def function_calls (self):
		return set ([fn for (n, fn) in self.function_call_addrs ()])

	def compile_hints (self, Problem):
		xs = ['Hints %s' % self.name]

		p = self.as_problem (Problem)

		for n in p.nodes:
			ys = ['VarDeps', str (n)]
			for (nm, typ) in p.var_deps[n]:
				ys.append (nm)
				typ.serialise (ys)
			xs.append (' '.join (ys))
			if self.nodes[n].kind != 'Basic':
				continue
		return xs

	def save_graph (self, fname):
		import problem
		problem.save_graph (self.nodes, fname)

def mk_builtinTs ():
	return dict([(n, Type('Builtin', n)) for n
	in 'Bool Mem Dom HTD PMS UNIT Type Token RelWrapper'.split()])
builtinTs = mk_builtinTs ()
boolT = builtinTs['Bool']
word32T = Type ('Word', '32')
word64T = Type ('Word', '64')
word8T = Type ('Word', '8')

phantom_types = set ([builtinTs[t] for t
	in 'Dom HTD PMS UNIT Type'.split ()])

def concrete_type (typ):
	if typ.kind == 'Ptr':
		return word32T
	else:
		return typ

global_wrappers = {}
def get_global_wrapper (typ):
	if typ in global_wrappers:
		return global_wrappers[typ]
	struct_name = fresh_name ('Global (%s)' % typ, structs)
	struct = Struct (struct_name, typ.size (), typ.align ())
	struct.add_field ('v', typ, 0)
	structs[struct_name] = struct

	global_wrappers[typ] = struct.typ
	return struct.typ

# ==========================================================
# parsing code for types, expressions, structs and functions

def parse_int (s):
	if s.startswith ('-') or s.startswith ('~'):
		return (- parse_int (s[1:]))
	if s.startswith ('0x') or s.startswith ('0b'):
		return int (s, 0)
	else:
		return int (s)

def parse_typ(bits, n, symbolic_types = False):
	if bits[n] == 'Word' or bits[n] == 'BitVec':
		return (n + 2, Type('Word', parse_int (bits[n + 1])))
	elif bits[n] == 'WordArray' or bits[n] == 'FloatingPoint':
		return (n + 3, Type(bits[n],
			parse_int (bits[n + 1]), parse_int (bits[n + 2])))
	elif bits[n] in builtinTs:
		return (n + 1, builtinTs[bits[n]])
	elif bits[n] == 'Array':
		(n, typ) = parse_typ (bits, n + 1, True)
		return (n + 1, Type ('Array', parse_int (bits[n]), typ))
	elif bits[n] == 'Struct':
		return (n + 2, Type ('Struct', bits[n + 1]))
	elif bits[n] == 'Ptr':
		(n, typ) = parse_typ (bits, n + 1, True)
		if symbolic_types:
			return (n, Type ('Ptr', '', typ))
		else:
			return (n, word32T)
	else:
		assert not 'type encoded', (n, bits[n:], bits)

def node_name (name):
	if name in {'Ret':True, 'Err':True}:
		return name
	else:
		try:
			return parse_int (name)
		except ValueError, e:
			assert not 'node name understood', name

def parse_list (parser, bits, n, extra=None):
	try:
		num = parse_int (bits[n])
	except ValueError:
		assert not 'number parseable', (n, bits[n:], bits)
	n = n + 1
	xs = []
	for i in range (num):
		if extra:
			(n, x) = parser(bits, n, extra)
		else:
			(n, x) = parser(bits, n)
		xs.append(x)
	return (n, xs)

def parse_arg (bits, n):
	nm = bits[n]
	(n, typ) = parse_typ (bits, n + 1)
	return (n, (nm, typ))

ops = {'Plus':2, 'Minus':2, 'Times':2, 'Modulus':2,
	'DividedBy':2, 'BWAnd':2, 'BWOr':2, 'BWXOR':2, 'And':2,
	'Or':2, 'Implies':2, 'Equals':2, 'Less':2,
	'LessEquals':2, 'SignedLess':2, 'SignedLessEquals':2,
	'ShiftLeft':2, 'ShiftRight':2, 'CountLeadingZeroes':1,
	'SignedShiftRight':2,
	'Not':1, 'BWNot':1, 'WordCast':1, 'WordCastSigned':1,
	'True':0, 'False':0, 'UnspecifiedPrecond':0,
	'MemUpdate':3, 'MemAcc':2, 'IfThenElse':3, 'ArrayIndex':2,
	'ArrayUpdate':3, 'MemDom':2,
	'PValid':3, 'PWeakValid':3, 'PAlignValid':2, 'PGlobalValid':3,
	'PArrayValid':4,
	'HTDUpdate':5, 'WordArrayAccess':2, 'WordArrayUpdate':3,
	'TokenWordsAccess':2, 'TokenWordsUpdate':3,
	'ROData':1, 'StackWrapper':2,
	'ToFloatingPoint':1, 'ToFloatingPointSigned':2,
	'ToFloatingPointUnsigned':2, 'FloatingPointCast':1, 
}

ops_to_smt = {'Plus':'bvadd', 'Minus':'bvsub', 'Times':'bvmul', 'Modulus':'bvurem',
	'DividedBy':'bvudiv', 'BWAnd':'bvand', 'BWOr':'bvor', 'BWXOR':'bvxor',
	'And':'and',
	'Or':'or', 'Implies':'=>', 'Equals':'=', 'Less':'bvult',
	'LessEquals':'bvule', 'SignedLess':'bvslt', 'SignedLessEquals':'bvsle',
	'ShiftLeft':'bvshl', 'ShiftRight':'bvlshr', 'SignedShiftRight':'bvashr',
	'Not':'not', 'BWNot':'bvnot',
	'True':'true', 'False':'false',
	'UnspecifiedPrecond': 'unspecified-precond',
	'IfThenElse':'ite', 'MemDom':'mem-dom',
	'ROData': 'rodata', 'ImpliesROData': 'implies-rodata',
	'WordArrayAccess':'select', 'WordArrayUpdate':'store'}

ex_smt_ops = """roundNearestTiesToEven RNE roundNearestTiesToAway RNA
    roundTowardPositive RTP roundTowardNegative RTN
    roundTowardZero RTZ
    fp.abs fp.ne fp.add fp.sub fp.mul fp.div fp.fma fp.sqrt fp.rem
    fp.roundToInteral fp.min fp.max fp.leq fp.lt fp.eq fp.t fp.eq
    fp.isNormal fp.IsSubnormal fp.isZero fp.isInfinite fp.isNaN
    fp.isNeative fp.isPositive""".split ()

ops_to_smt.update (dict ([(smt, smt) for smt in ex_smt_ops]))

smt_to_ops = dict ([(smt, oper) for (oper, smt) in ops_to_smt.iteritems ()])

def parse_struct_elem (bits, n):
	name = bits[n]
	(n, typ) = parse_typ (bits, n + 1)
	(n, val) = parse_expr (bits, n)
	return (n, (name, val))

def parse_expr (bits, n):
	if bits[n] in set (['Symbol', 'Var', 'ConstGlobal', 'Token']):
		kind = bits[n]
		name = bits[n + 1]
		(n, typ) = parse_typ (bits, n + 2)
		return (n, Expr (kind, typ, name = name))
	if bits[n] == 'Array':
		(n, typ) = parse_typ (bits, n + 1)
		assert typ.kind == 'Array'
		(n, xs) = parse_list (parse_expr, bits, n)
		assert len(xs) == typ.num
		return (n, Expr ('Array', typ, vals = xs))
	elif bits[n] == 'Field':
		(n, typ) = parse_typ (bits, n + 1)
		name = bits[n]
		(n, typ2) = parse_typ (bits, n + 1)
		(n, struct) = parse_expr (bits, n)
		assert struct.typ == typ
		return (n, Expr ('Field', typ2, struct = struct,
			field = (name, typ2)))
	elif bits[n] == 'FieldUpd':
		(n, typ) = parse_typ (bits, n + 1)
		name = bits[n]
		(n, typ2) = parse_typ (bits, n + 1)
		(n, val) = parse_expr (bits, n)
		(n, struct) = parse_expr (bits, n)
		return (n, Expr ('FieldUpd', typ, struct = struct,
			field = (name, typ2), val = val))
	elif bits[n] == 'StructCons':
		(n, typ) = parse_typ (bits, n + 1)
		(n, xs) = parse_list (parse_struct_elem, bits, n)
		return (n, Expr ('StructCons', typ, vals = dict(xs)))
	elif bits[n] == 'Num':
		v = parse_int (bits[n + 1])
		(n, typ) = parse_typ (bits, n + 2)
		return (n, Expr ('Num', typ, val = v))
	elif bits[n] == 'Op':
		op = bits[n + 1]
		op = smt_to_ops.get (op, op)
		assert op in ops, op
		(n, typ) = parse_typ (bits, n + 2)
		(n, xs) = parse_list (parse_expr, bits, n)
		assert len (xs) == ops[op]
		return (n, Expr ('Op', typ, name = op, vals = xs))
	elif bits[n] == 'Type':
		(n, typ) = parse_typ (bits, n + 1, symbolic_types = True)
		return (n, Expr ('Type', builtinTs['Type'], val = typ))
	else:
		assert not 'expr parseable', (n, bits[n : n + 3], bits)

def parse_lval (bits, n):
	name = bits[n]
	(n, typ) = parse_typ (bits, n + 1)
	return (n, (name, typ))

def parse_lval_and_val (bits, n):
	(n, (name, typ)) = parse_lval (bits, n)
	(n, val) = parse_expr (bits, n)
	return (n, ((name, typ), val))

def parse_node (bits, n):
	if bits[n] == 'Basic':
		cont = node_name(bits[n + 1])
		(n, upds) = parse_list (parse_lval_and_val, bits, n + 2)
		return Node ('Basic', cont, upds)
	elif bits[n] == 'Cond':
		left = node_name(bits[n + 1])
		right = node_name(bits[n + 2])
		(n, cond) = parse_expr (bits, n + 3)
		return Node ('Cond', (left, right), cond)
	else:
		assert bits[n] == 'Call'
		cont = node_name(bits[n + 1])
		name = bits[n + 2]
		(n, args) = parse_list (parse_expr, bits, n + 3)
		(n, saves) = parse_list (parse_lval, bits, n)
		return Node ('Call', cont, (name, args, saves))

true_term = Expr ('Op', boolT, name = 'True', vals = [])
false_term = Expr ('Op', boolT, name = 'False', vals = [])
unspecified_precond_term = Expr ('Op', boolT, name = 'UnspecifiedPrecond', vals = [])

def parse_all(lines):
	'''Toplevel parser for input information. Accepts an iterator over
lines. See syntax.quick_reference for an explanation.'''

	structs = {}
	functions = {}
	const_globals = {}
	for line in lines:
		bits = line.split()
		# empty lines and #-comments ignored
		if not bits or bits[0][0] == '#':
			continue
		if bits[0] == 'Struct':
			# Struct <name> <size> <alignment>
			# followed by block of StructField lines
			assert bits[1] not in structs
			current_struct = Struct (bits[1], parse_int (bits[2]),
				parse_int (bits[3]))
			structs[bits[1]] = current_struct
		elif bits[0] == 'StructField':
			# StructField <name> <type (encoded)> <offset>
			(_, typ) = parse_typ(bits, 2, symbolic_types = True)
			current_struct.add_field (bits[1], typ,
				parse_int (bits[-1]))
		elif bits[0] == 'ConstGlobalDef':
			# ConstGlobalDef <name> <value>
			name = bits[1]
			(_, val) = parse_expr (bits, 2)
			const_globals[name] = val
		elif bits[0] == 'Function':
			# Function <name> <inputs> <outputs>
			# followed by optional block of node lines
			# concluded by EntryPoint line
			(n, inputs) = parse_list (parse_arg, bits, 2)
			(_, outputs) = parse_list (parse_arg, bits, n)
			trace ('Function %s' % bits[1])
			current_function = Function (bits[1], inputs, outputs)
			functions[bits[1]] = current_function
		elif bits[0] == 'EntryPoint':
			# EntryPoint <entry point>
			entry = node_name(bits[1])
			# instead of setting function.entry to this value,
			# create a dummy node. this ensures there is always
			# at least one node (EntryPoint Ret is valid) and
			# also that the entry point is not in a loop
			name = fresh_node (current_function.nodes)
			current_function.nodes[name] = Node ('Basic',
				entry, [])
			current_function.entry = name
			# ensure that the function graph is closed
			check_cfg (current_function)
			current_function = None
		else:
			# <node name> <node (encoded)>
			name = node_name(bits[0])
			assert name not in current_function.nodes, (name, bits)
			current_function.nodes[name] = parse_node (bits, 1)

	return (structs, functions, const_globals)

def parse_and_install_all (lines, tag, skip_functions=None):
	if skip_functions == None:
	    skip_functions = []
	(structs, functions, const_globals) = parse_all (lines)
	for f in skip_functions:
	    if f in functions:
		del functions[f]
	target_objects.structs.update (structs)
	target_objects.functions.update (functions)
	target_objects.const_globals.update (const_globals)
	if tag != None:
		target_objects.functions_by_tag[tag] = set (functions)
	return (structs, functions, const_globals)

# ===============================
# simple accessor code and checks

def visit_rval (vs):
	def visit (expr):
		if expr.kind == 'Var':
			v = expr.name
			if v in vs:
				assert vs[v] == expr.typ, (expr, vs[v])
			vs[v] = expr.typ
		if expr.is_op ('MemAcc'):
			[m, p] = expr.vals
			assert p.typ == word32T, expr
		if expr.is_op ('PGlobalValid'):
			[htd, typ_expr, p] = expr.vals
			typ = typ_expr.val
			get_global_wrapper (typ)

	return visit

def visit_lval (vs):
	def visit ((name, typ)):
		assert vs.get(name, typ) == typ, (name, vs[name], typ)
		vs[name] = typ

	return visit

def get_expr_vars (expr, vs):
	expr.visit (visit_rval (vs))

def get_expr_var_set (expr):
	vs = {}
	get_expr_vars (expr, vs)
	return set (vs.items ())

def get_lval_vars (lval, vs):
	assert len(lval) == 2
	assert vs.get(lval[0], lval[1]) == lval[1]
	vs[lval[0]] = lval[1]

def get_node_vars (node, vs):
	node.visit (visit_lval (vs), visit_rval (vs))

def get_node_rvals (node, vs = None):
	if vs == None:
		vs = {}
	node.visit (lambda l: (), visit_rval (vs))
	return vs

def get_vars(function):
	vs = dict(function.inputs + function.outputs)
	for node in function.nodes.itervalues():
		get_node_vars(node, vs)
	return vs

def get_lval_typ(lval):
	assert len(lval) == 2
	return lval[1]

def get_expr_typ(expr):
	return expr.typ

def check_cfg (fun):
	dead_arcs = [(n, n2) for (n, node) in fun.nodes.iteritems ()
		for n2 in node.get_conts ()
		if n2 not in fun.nodes and n2 not in ['Ret', 'Err']]
	for (n, n2) in dead_arcs:
		trace ('Warning: dead arc in %s: %s -> %s'
			% (fun.name, n, n2))
		if fun.nodes[n].kind == 'Call':
			trace ('  (follows call to %s)' % fun.nodes[n].fname)
		else:
			trace ('  (follows %s node!)' % fun.nodes[n].kind)
		assert type (n2) != str
		# OK if multiple dead arcs and we save over n2 twice
		fun.nodes[n2] = Node ('Basic', 'Err', [])

def check_funs (functions, verbose = False):
	for (f, fun) in functions.iteritems():
		if not fun:
			continue
		if verbose:
			trace ('Checking %s' % f)
		check_cfg (fun)
		get_vars(fun)
		for (n, node) in fun.nodes.iteritems():
			if node.kind == 'Call':
				c = functions[node.fname]
				assert map(get_expr_typ, node.args) == \
					map (get_lval_typ, c.inputs), (
						 node.fname, node.args, c.inputs)
				assert map (get_lval_typ, node.rets) == \
					map (get_lval_typ, c.outputs), (
						 node.fname, node.rets, c.outputs)
			elif node.kind == 'Basic':
				for (lv, v) in node.upds:
					assert get_lval_typ(lv) == get_expr_typ(v)
			elif node.kind == 'Cond':
				assert get_expr_typ(node.cond) == boolT

def get_extensions (v):
	extensions = set ()
	rm = builtinTs['RoundingMode']
	def visitor (expr):
		if expr.typ == rm or expr.typ.kind == 'FloatingPoint':
			extensions.add ('FloatingPoint')
	v.gen_visit (lambda l: (), visitor)
	return extensions

# =========================================
# common constructors for basic expressions

def mk_var (nm, typ):
	return Expr ('Var', typ, name = nm)

def mk_token (nm):
	return Expr ('Token', builtinTs['Token'], name = nm)

def mk_plus (x, y):
	assert x.typ == y.typ
	return Expr ('Op', x.typ, name = 'Plus', vals = [x, y])

def mk_uminus (x):
	zero = Expr ('Num', x.typ, val = 0)
	return mk_minus (zero, x)

def mk_minus (x, y):
	assert x.typ == y.typ
	return Expr ('Op', x.typ, name = 'Minus', vals = [x, y])

def mk_times (x, y):
	assert x.typ == y.typ
	return Expr ('Op', x.typ, name = 'Times', vals = [x, y])

def mk_modulus (x, y):
	assert x.typ == y.typ
	return Expr ('Op', x.typ, name = 'Modulus', vals = [x, y])

def mk_bwand (x, y):
	assert x.typ == y.typ
	assert x.typ.kind == 'Word'
	return Expr ('Op', x.typ, name = 'BWAnd', vals = [x, y])

def mk_eq (x, y):
	assert x.typ == y.typ
	return Expr ('Op', boolT, name = 'Equals', vals = [x, y])

def mk_less_eq (x, y):
	assert x.typ == y.typ
	return Expr ('Op', boolT, name = 'LessEquals', vals = [x, y])

def mk_less (x, y):
	assert x.typ == y.typ
	return Expr ('Op', boolT, name = 'Less', vals = [x, y])

def mk_implies (x, y):
	assert x.typ == boolT
	assert y.typ == boolT
	return Expr ('Op', boolT, name = 'Implies', vals = [x, y])

def mk_and (x, y):
	assert x.typ == boolT
	assert y.typ == boolT
	return Expr ('Op', boolT, name = 'And', vals = [x, y])

def mk_or (x, y):
	assert x.typ == boolT
	assert y.typ == boolT
	return Expr ('Op', boolT, name = 'Or', vals = [x, y])

def mk_not (x):
	assert x.typ == boolT
	return Expr ('Op', boolT, name = 'Not', vals = [x])

def mk_shift_gen (name, x, n):
	assert x.typ.kind == 'Word'
	if type (n) == int:
		n = Expr ('Num', x.typ, val = n)
	return Expr ('Op', x.typ, name = name, vals = [x, n])

mk_shiftr = lambda x, n: mk_shift_gen ('ShiftRight', x, n)

def mk_clz (x):
	return Expr ('Op', word32T, name = "CountLeadingZeroes", vals = [x])

def mk_ctz (x):
	# if x = 0, ctz = <x-width>
	# otherwise (x & -x) has one 1 and the same trailing zeroes,
	# subtract from leading zeroes
	return mk_if (mk_eq (x, mk_word32 (0)), mk_word32 (x.typ.num),
		mk_minus (mk_word32 (x.typ.num - 1),
			mk_clz (mk_bwand (x, mk_uminus (x)))))

def foldr1 (f, xs):
	x = xs[-1]
	for i in reversed (range (len (xs) - 1)):
		x = f (xs[i], x)
	return x

def mk_num (x, typ):
	import logic
	if logic.is_int (typ):
		typ = Type ('Word', typ)
	assert typ.kind == 'Word', typ
	assert logic.is_int (x), x
	return Expr ('Num', typ, val = x)

def mk_word32 (x):
	return mk_num (x, word32T)

def mk_word8 (x):
	return mk_num (x, word8T)

def mk_word32_maybe(x):
	import logic
	if logic.is_int (x):
		return mk_word32 (x)
	else:
		assert x.typ == word32T
		return x

def mk_cast (x, typ):
	if x.typ == typ:
		return x
	else:
		assert x.typ.kind == 'Word', x.typ
		assert typ.kind == 'Word', typ
		return Expr ('Op', typ, name = 'WordCast', vals = [x])

def mk_memacc(m, p, typ):
	assert m.typ == builtinTs['Mem']
	assert p.typ == word32T
	return Expr ('Op', typ, name = 'MemAcc', vals = [m, p])

def mk_memupd(m, p, v):
	assert m.typ == builtinTs['Mem']
	assert p.typ == word32T
	return Expr ('Op', m.typ, name = 'MemUpdate', vals = [m, p, v])

def mk_arr_index (arr, i):
	assert arr.typ.kind == 'Array'
	return Expr ('Op', arr.typ.el_typ, name = 'ArrayIndex',
		vals = [arr, i])

def mk_arroffs(p, typ, i):
	assert typ.kind == 'Array'
	import logic
	if logic.is_int (i):
		assert i < typ.num
		offs = i * typ.el_typ.size()
		assert offs == i or offs % 4 == 0
		return mk_plus (p, mk_word32 (offs))
	else:
		sz = typ.el_typ.size()
		return mk_plus (p, mk_times (i, mk_word32 (sz)))

def mk_if (P, x, y):
	assert P.typ == boolT
	assert x.typ == y.typ
	return Expr ('Op', x.typ, name = 'IfThenElse', vals = [P, x, y])

def mk_meta_typ (typ):
	return Expr ('Type', builtinTs['Type'], val = typ)

def mk_pvalid (htd, typ, p):
	return Expr ('Op', boolT, name = 'PValid',
		vals = [htd, mk_meta_typ (typ), p])

def mk_rel_wrapper (nm, vals):
	return Expr ('Op', builtinTs['RelWrapper'], name = nm, vals = vals)

mks = (mk_var, mk_plus, mk_uminus, mk_minus, mk_times, mk_modulus, mk_bwand,
mk_eq, mk_less_eq, mk_less, mk_implies, mk_and, mk_or, mk_not, mk_word32,
mk_word8, mk_word32_maybe, mk_cast, mk_memacc, mk_memupd, mk_arr_index,
mk_arroffs, mk_if, mk_meta_typ, mk_pvalid)

# ====================================================================
# pretty printing code for the syntax - only used for printing reports

def pretty_type (typ):
	if typ.kind == 'Word':
		return 'Word%d' % typ.num
	elif typ.kind == 'WordArray':
		[ix, num] = typ.nums
		return 'Word%d[%d]' % (num, ix)
	elif typ.kind == 'Ptr':
		return 'Ptr(%s)' % pretty_type (typ.el_typ_symb)
	elif typ.kind == 'Struct':
		return 'struct %s' % typ.name
	elif typ.kind == 'Builtin':
		return typ.name
	else:
		assert not 'type pretty-printable', typ

pretty_opers = {'Plus': '+', 'Minus': '-', 'Times': '*'}

known_typ_change = set (['ROData', 'MemAcc', 'IfThenElse', 'WordArrayUpdate',
	'MemDom'])

def pretty_expr (expr, print_type = False):
	if print_type:
		return '((%s) (%s))' % (pretty_type (expr.typ),
			pretty_expr (expr))
	elif expr.kind == 'Var':
		return repr (expr.name)
	elif expr.kind == 'Num':
		return '%d' % expr.val
	elif expr.kind == 'Op' and expr.name in pretty_opers:
		[x, y] = expr.vals
		return '(%s %s %s)' % (pretty_expr (x), pretty_opers[expr.name],
			pretty_expr (y))
	elif expr.kind == 'Op':
		if expr.name in known_typ_change:
			vals = [pretty_expr (v) for v in expr.vals]
		else:
			vals = [pretty_expr (v, print_type = v.typ != expr.typ)
				for v in expr.vals]
		return '%s(%s)' % (expr.name, ', '.join (vals))
	elif expr.kind == 'Token':
		return "''%s''" % expr.name
	else:
		assert not 'expr pretty-printable', expr


# =================================================
# some helper code that's needed all over the place

def fresh_name (n, D, v=True):
	if n not in D:
		D[n] = v
		return n

	x = 1
	y = 1
	while ('%s.%d' % (n, x)) in D:
		y = x
		x = x * 2
	while y < x:
		z = (y + x) / 2
		if ('%s.%d' % (n, z)) in D:
			y = z + 1
		else:
			x = z
	n = '%s.%d' % (n, x)
	assert n not in D

	D[n] = v
	return n

def fresh_node (ns, hint = 1):
	n = hint
	# use names that are *not* multiples of 4
	n = (n | 15) + 2
	while n in ns:
		n += 16
	return n

