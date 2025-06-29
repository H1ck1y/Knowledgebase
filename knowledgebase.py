

# Include your imports here, if any are used.
import time
import itertools
import copy



class Expr(object):
    def __hash__(self):
        return hash((type(self).__name__, self.hashable))

class Atom(Expr):
    def __init__(self, name):
        self.name = name
        self.hashable = name

    def __hash__(self):
        return hash((self.hashable,type(self)))

    def __eq__(self, other):
        return isinstance(other, Atom) and (self.name == other.name)

    def __repr__(self):
        return "Atom(" + str(self.name) + ")"

    def atom_names(self):
        return {self.name}

    def evaluate(self, assignment):
        return assignment[self.name]

    def to_cnf(self):
        return self

class Not(Expr):
    def __init__(self, arg):
        self.arg = arg
        self.hashable = arg

    def __hash__(self):
        return hash((self.hashable,type(self)))

    def __eq__(self, other):
        return isinstance(other, Not) and (self.arg == other.arg)

    def __repr__(self):
        return "Not(" + str(self.arg) + ")"

    def atom_names(self):
        name_set = set()
        name_set.update(self.arg.atom_names())
        return name_set

    def evaluate(self, assignment):
        return not(self.arg.evaluate(assignment))

    def to_cnf(self):
            element = self.arg.to_cnf()
            if isinstance(element, Atom):
                return self
            elif isinstance(element,Not):
                return element.arg.to_cnf()
            elif isinstance(element,And):
                not_object = []
                for item in element.conjuncts:
                    newobject = Not(item)
                    not_object.append(newobject)
                return Or(*not_object).to_cnf()
            elif isinstance(element, Or):
                not_object = []
                for item in element.disjuncts:
                    newobject = Not(item)
                    not_object.append(newobject)
                return And(*not_object).to_cnf()



class And(Expr):
    def __init__(self, *conjuncts):
        self.conjuncts = frozenset(conjuncts)
        self.hashable = self.conjuncts
        self.plist = list(conjuncts)

    def __hash__(self):
        return hash((self.hashable,type(self)))

    def __eq__(self, other):
        return isinstance(other,And) and (self.conjuncts == other.conjuncts)

    def __repr__(self):
        return "And(" + ", ".join(repr(i) for i in self.plist) + ")"

    def atom_names(self):
        name_set = set()
        for element in self.plist:
            name_set.update(element.atom_names())
        return name_set

    def evaluate(self, assignment):
        for element in self.conjuncts:
            if element.evaluate(assignment) == False:
                return False
        return  True


    def to_cnf(self):
        new_set = set()
        for element in self.conjuncts:
            new = element.to_cnf()
            if isinstance(new, And):
                new_set.update(new.conjuncts)
            else:
                new_set.add(new)
        return And(*new_set)

class Or(Expr):
    def __init__(self, *disjuncts):
        self.disjuncts = frozenset(disjuncts)
        self.hashable = self.disjuncts
        self.plist = list(disjuncts) #used for order printing

    def __hash__(self):
        return hash((self.hashable,type(self)))

    def __eq__(self, other):
        return isinstance(other,Or) and (self.disjuncts == other.disjuncts)

    def __repr__(self):
        return "Or(" + ", ".join(repr(i) for i in self.plist) + ")"

    def atom_names(self):
        name_set = set()
        for element in self.plist:
            name_set.update(element.atom_names())
        return name_set

    def evaluate(self, assignment):
        for element in self.disjuncts:
            if element.evaluate(assignment) == True:
                return True
        return False

    def to_cnf(self):
        new_disjuncts = []
        for item in self.plist:
            cnf_item = item.to_cnf()
            if isinstance(cnf_item, Or):
                new_disjuncts.extend(cnf_item.plist)
            else:
                new_disjuncts.append(cnf_item)

        and_groups = []
        others = []
        for x in new_disjuncts:
            if isinstance(x, And):
                and_groups.append(list(x.conjuncts))
            else:
                others.append(x)

        if and_groups:
            combinations = itertools.product(*and_groups)
            result = []
            for combo in combinations:
                combined = list(combo) + others
                result.append(Or(*combined).to_cnf())
            return And(*result)
        return Or(*others)


class Implies(Expr):
    def __init__(self, left, right):
        self.left = left
        self.right = right
        self.hashable = (left, right)
        self.plist = list(self.hashable)

    def __hash__(self):
        return hash((self.hashable,type(self)))

    def __eq__(self, other):
        return isinstance(other,Implies) and (self.left == other.left) and (self.right == other.right)

    def __repr__(self):
        return "Implies(" + ", ".join(repr(i) for i in self.plist) + ")"

    def atom_names(self):
        name_set = set()
        for element in self.plist:
            name_set.update(element.atom_names())
        return name_set

    def evaluate(self, assignment):
        if (self.right.evaluate(assignment) == False) and (self.left.evaluate(assignment) == True) :
                return False
        return True

    def to_cnf(self):
        parameter = [Not(self.left), self.right]
        return Or(*parameter).to_cnf()

class Iff(Expr):
    def __init__(self, left, right):
        self.left = left
        self.right = right
        self.hashable = (left, right)
        self.plist = list(self.hashable)

    def __hash__(self):
        return hash((self.hashable, type(self)))

    def __eq__(self, other):
         return isinstance(other, Iff) and ((self.left, self.right) == (other.left, other.right))

    def __repr__(self):
        return "Iff(" + ", ".join(repr(i) for i in self.plist) + ")"

    def atom_names(self):
        name_set = set()
        for element in self.plist:
            name_set.update(element.atom_names())
        return name_set

    def evaluate(self, assignment):
        if (self.left.evaluate(assignment) == self.right.evaluate(assignment)):
            return  True
        else:
            return  False

    def to_cnf(self):
        p1 = Or(Not(self.left), self.right)  # ¬A ∨ B
        p2 = Or(Not(self.right), self.left)  # ¬B ∨ A
        return And(p1.to_cnf(), p2.to_cnf()).to_cnf()


def satisfying_assignments(expr):
    answer_set = expr.atom_names()
    listb = [True, False]
    all_possible_comb = itertools.product(listb , repeat=len(answer_set))
    for values in all_possible_comb:
        answer_dict = dict(zip(answer_set, values))
        if expr.evaluate(answer_dict):
            yield answer_dict

class KnowledgeBase(object):
    def __init__(self):
        self.facts = set()

    def get_facts(self):
        return self.facts

    def tell(self, expr):
        new_expr = expr.to_cnf()
        if isinstance(new_expr, And):
            for item in new_expr.conjuncts:
                self.facts.add(item)
        else:
            self.facts.add(new_expr)

    def resolve(self, a, b):
        setA = set()
        setB = set()
        resolvent = set()

        if isinstance(a, Or):
            setA.update(a.disjuncts)
        else:
            setA.add(a)

        if isinstance(b, Or):
            setB.update(b.disjuncts)
        else:
            setB.add(b)

        for item in setA:
            for item2 in setB:
                if (item == Not(item2)) or (item2 == Not(item)):
                    rest1 = setA.copy()
                    rest2 = setB.copy()
                    rest1.remove(item)
                    rest2.remove(item2)
                    merged = rest1.union(rest2)

                    if len(merged) == 0:
                        resolvent.add("empty")
                    else:
                        if len(merged) == 1:
                            resolvent.add(list(merged)[0])
                        else:
                            resolvent.add(Or(*merged))
        return resolvent

    def checkorT(self,clause):
        if isinstance(clause, Or):
            literals = clause.disjuncts
            for item in literals:
                if isinstance(item, Not):
                    if item.arg in literals:
                        return True
                else:
                    if Not(item) in literals:
                        return True
        return False

    def resolution_algorithm(self, alpha):
        clauses = set(self.facts)
        new_alpha = Not(alpha).to_cnf()
        clauses.add(new_alpha)
        clause_list = list(clauses)

        TIMEOUT = 5
        start_time = time.time()

        while True:
            #protection infinite loops sometimes
            #if time.time() - start_time > TIMEOUT:
                #return False

            next_new = set()

            for i in range(len(clause_list)):
                for j in range(i + 1, len(clause_list)):
                    i2 = clause_list[i]
                    j2 = clause_list[j]
                    resolvents = self.resolve(i2, j2)
                    if "empty" in resolvents:
                        return True

                    for res in resolvents:
                        if not self.checkorT(res) and res not in clauses:
                            next_new.add(res)

                    #protection, infinite loop sometimes
                    #if time.time() - start_time > TIMEOUT:
                       # return False

            if not next_new:
                return False

            clauses.update(next_new)
            clause_list = list(clauses)


    def ask(self, expr):
        return self.resolution_algorithm(expr)





# Puzzle 1

# Populate the knowledge base using statements of the form kb1.tell(...)
kb1 = KnowledgeBase()
Expr1 = Implies(Atom("mythical"), Not(Atom("mortal")))
Expr2 = Implies(Not(Atom("mythical")), And(Atom("mortal"),Atom("mammal")))
Expr3 = Implies(Or(Not(Atom("mortal")), Atom("mammal")), Atom("horned"))
Expr4 = Implies(Atom("horned"), Atom("magical"))

kb1.tell(Expr1)
kb1.tell(Expr2)
kb1.tell(Expr3)
kb1.tell(Expr4)

# Write an Expr for each query that should be asked of the knowledge base
mythical_query = Atom("mythical")
magical_query =  Atom("magical")
horned_query = Atom("horned")


#print(kb1.ask(mythical_query))
#print(kb1.ask(magical_query))
#print(kb1.ask(horned_query))

is_mythical = False
is_magical = True
is_horned = True

# Puzzle 2

a = Atom("a")
j = Atom("j")
m = Atom("m")

a1 = Implies(Or(m, a), j)
a2 = Implies(Not(m), a)
a3 = Implies(a, Not(j))

party_constraints = And(a1,a2,a3)

# Compute a list of the valid attendance scenarios using a call to
# satisfying_assignments(expr)
valid_scenarios = list(satisfying_assignments(party_constraints))
# print(valid_scenarios)

# Write your answer to the question in the assignment
puzzle_2_question = """
Anna: does not come
Mary: come
john: come
"""

# Puzzle 3

# Populate the knowledge base using statements of the form kb3.tell(...)
kb3 = KnowledgeBase()

p1 = Atom('p1')
p2 = Atom('p2')
e1 = Atom('e1')
e2 = Atom('e2')
s1 = Atom('s1')
s2 = Atom('s2')


door1says = And(p1, e2)
relationship1 = Iff(s1, door1says)

door2says = And(Or(p1, p2), Or(e1, e2))
relationship2 = Iff(s2, door2says)

rule1 = Iff(p1,Not(e1))
rule2 = Iff(p2,Not(e2))
rule3 = Iff(s1, Not(s2))


kb3.tell(relationship1)
kb3.tell(relationship2)
kb3.tell(rule1)
kb3.tell(rule2)
kb3.tell(rule3)


#print(kb3.get_facts())

#print(kb3.ask(s1)) 
#print(kb3.ask(s2))
#print(kb3.ask(e1))
#print(kb3.ask(e2))


puzzle_3_question = """
#door 1 says door1 has prize and room2 is empty
iff s1 correct, then door1says correct

#door 2 says at least one room is empty and at least one room has prize

#iff room1 has prize, then room1 cannot be empty
#iff room2 has prize, then room2 cannot be empty
#iff door2 has tells truth, then door1 lies
door2 has prize, and door1 is empty.
"""

# Puzzle 4

# Populate the knowledge base using statements of the form kb4.tell(...)
kb4 = KnowledgeBase()
ia = Atom('ia')
ib = Atom('ib')
ic = Atom('ic')
ka = Atom('ka')
kb_ = Atom('kb')
kc = Atom('kc')

rule1 = Implies(ia, And(kb_, Not(kc)))
rule2 = Implies(ib, Not(kb_))
rule3 = Implies(ic, And(ka, kb_))
rule4 = Or(And (ia,  ib, Not(ic)),And(ia, Not(ib), ic),And(Not(ia), ib, ic))




kb4.tell(rule1)
kb4.tell(rule2)
kb4.tell(rule3)
kb4.tell(rule4)

#print(kb4.ask(ia))
#print(kb4.ask(ib))
#print(kb4.ask(ic))

# Uncomment the line corresponding to the guilty suspect
# guilty_suspect = "Adams"
guilty_suspect = "Brown"
# guilty_suspect = "Clark"


puzzle_4_question = """
#rule1 = And(Or(Not(ia), kb_),Or(Not(ia), Not(kc))) this is the first guy says: if a is not inocent then b is familiar with the guy
        and c does not know the guy
#rule2 = if  b is inoocent, then b does not know they guy
#rule3 = if c is innocentl, then both a and b know that guy
#rule4 = only one guy is guilty
Brown is guilty since ia returns True, ic returns True and ib returns False
"""



