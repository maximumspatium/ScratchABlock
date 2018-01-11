import copy
import logging

from graph import Graph
from core import *
import cfgutils
import dot

log = logging.getLogger(__name__)


def split_bblock(cfg, n):
    # If a node is non-empty bblock, splits it in two, with 2nd one being
    # empty, and having all out edges, and returns this 2nd one. If bblock
    # is already empty, returns it directly.
    if not cfg[n]["val"].items:
        return n
    addr = n + ".if"
    pre = BBlock(addr)
    cfg.add_node(addr, val=pre)
    cfg.move_succ(n, addr)
    cfg.add_edge(n, addr)
    return addr


def split_node(cfg, n):
    """Split node "horizontally", by duplicating its content and splitting
    incoming and outgoing edges.
    """
    assert cfg.degree_in(n) == 2
    assert cfg.degree_out(n) == 1
    preds = cfg.pred(n)
    node_props = cfg[n]
    node2_props = copy.deepcopy(node_props)
    n2 = n + ".split1"
    cfg.add_node(n2, **node2_props)
    cfg.remove_edge(preds[1], n)
    cfg.add_edge(preds[1], n2)
    cfg.add_edge(n2, cfg.succ(n)[0])


class RecursiveBlock(BBlock):
    """A structured block, consisting recursively of BBlock's and
    RecursiveBlock's."""

    def recursive_union(self, func):
        res = set()
        for subb in self.subblocks():
            res |= func(subb)
        return res

    def uses(self):
        return self.recursive_union(lambda b: b.uses())

    def defs(self, regs_only=True):
        return self.recursive_union(lambda b: b.defs(regs_only))


class Seq(RecursiveBlock):
    def __init__(self, b1, b2):
        super().__init__(b1.addr)
        self.items = [b1, b2]

    def subblocks(self):
        return self.items

    def __repr__(self):
        return "%s(%r, %r)" % (self.__class__.__name__, self.items[0], self.items[1])

    def dump(self, stream, indent=0, printer=str):
        for b in self.items:
            b.dump(stream, indent, printer)


def match_seq(cfg):
    for v, _ in cfg.iter_nodes():
        if cfg.degree_out(v) == 1:
            succ = cfg.succ(v)[0]
            if cfg.degree_in(succ) == 1:
                log.info("seq: %s %s", v, succ)
                newb = Seq(cfg.node(v)["val"], cfg.node(succ)["val"])
                cfg.add_node(v, val=newb)
                cfg.move_succ(succ, v)
                cfg.remove_node(succ)
                return True


class Switch(BBlock):
    def __init__(self, bstart, expr, cases, default):
        super().__init__(bstart.addr)
        self.expr = expr
        self.cases = cases
        self.default = default

    def subblocks(self):
        return self.cases + self.default

    def __repr__(self):
        return BBlock.__repr__(self)

    def dump(self, stream, indent=0, printer=str):
        self.write(stream, indent, "switch(%s) {" % self.expr)
        # dump cases
        for c in self.cases:
            self.write(stream, indent + 1, "case %s:" % c.sel)
            c.stmt.write(stream, indent + 2, printer)
            if c.has_break:
                self.write(stream, indent + 2, "break;")
        self.write(stream, indent, "}")


def match_switch_btree(cfg):
    with open("ggrrff.dot", 'w') as df:
            dot.dot(cfg, df, True, True)

    tconds = {}

    # collect CFG nodes whose reaching condition is
    # a comparison with a constant. Group them according
    # to their LHS expressions.
    for v, _ in cfg.iter_nodes():
        if cfg.degree_out(v) == 2:
            a, _ = cfg.sorted_succ(v)
            e1 = cfg.edge(v, a)
            e1_cond = e1.get('cond')
            if isinstance(e1_cond.expr.args[1], VALUE):
                k = e1_cond.expr.args[0]
                # WARNING: Dirty hack! remove TYPE cast if any
                if isinstance(k, EXPR) and isinstance(k.args[0], TYPE):
                    k = k.args[1]
                if k not in tconds:
                    tconds[k] = [(e1, v, a)]
                else:
                    tconds[k].append((e1, v, a))

    # reject expressions with less than 3 comparisons
    cand = dict(filter(lambda x: (len(x[1]) >= 3), tconds.items()))

    # consider EXPR == VALUE to be 'case' candidates
    cases = []
    for key in cand.keys():
        for val in cand[key]:
            cond = val[0].get('cond')
            if cond.expr.op == '==':
                case_node = val[2]
                cases.append((cond, case_node))

        if len(cases) < 3:
            return False

        log.info("Found %s cases:", len(cases))
        for c in cases:
            log.info("Case candidate node %s, expression: %s", c[1], c[0])

        # DFS over the switch tree and classify nodes into three categories:
        # - search nodes participating in binary search
        # - leaf nodes will become actual 'case' statements
        # - condition-less nodes with only one successor will become
        # 'default' candidates.
        wl = []
        def_nodes = []
        search_nodes = []
        leaf_nodes = []
        for pvc in cand[key]:
            if pvc[0].get('cond').expr.op != '==':
                succs = cfg.sorted_succ(pvc[1])
                wl.append((pvc[1], succs[0]))
                wl.append((pvc[1], succs[1]))
                break
            else:
                succs = cfg.sorted_succ(pvc[1])
                search_nodes.append(pvc[1])
                leaf_nodes.append(pvc[2])
                for s in succs:
                    wl.append((pvc[1], s))

        while wl:
            f, t = wl.pop(0)
            edge = cfg.edge(f, t)
            if f not in search_nodes:
                search_nodes.append(f)
            cond = edge.get('cond')
            succs = cfg.sorted_succ(t)
            if cond:
                if cond.expr.op in ['<', '<=', '=>', '>']:
                    wl.append((t, succs[0]))
                    wl.append((t, succs[1]))
                elif cond.expr.op == '==':
                    if t not in leaf_nodes:
                        leaf_nodes.append(t)
                else:
                    log.info("Huh?")
            else:
                if len(succs) == 1:
                    if t not in search_nodes:
                        search_nodes.append(t)
                    n = succs[0]
                    if n not in def_nodes:
                        def_nodes.append(n)
                    #log.info('Candidate default node: %s', n)
                else:
                    wl.append((t, succs[0]))
                    wl.append((t, succs[1]))

        if len(def_nodes) == 1:
            log.info("Found 'default' node: %s", def_nodes[0])
        else:
            log.info("Ambiguous 'default' (found several nodes)", def_nodes)
            #return False

        #for n in search_nodes:
        #    node = cfg.node(n)
        #    log.info("Search node #%s, label: %s", n, node.get('val').label)

        #for n in leaf_nodes:
        #    node = cfg.node(n)
        #    log.info("Leaf(case) node #%s, label: %s", n, node.get('val').label)

        # construct 'case' tuples (sel, stmt, has_break)
        ncases = []
        for n in leaf_nodes:
            for c in cand[key]:
                if n == c[2]:
                    edge = cfg.edge(c[1], c[2])
                    cond = edge.get('cond')
                    sel = cond.expr.args[1]
                    ncases.append((sel, cfg.node(n).get('val'), True))
                    break

        # replace all related CFG nodes with a collapsed switch node
        swstart = search_nodes[0]
        for n in search_nodes:
            if n != swstart:
                cfg.remove_node(n)
        #nb = split_bblock(cfg, swstart)
        nb = swstart
        for l in leaf_nodes:
            cfg.add_edge(nb, l)

        with open("ddbbgg.dot", 'w') as df:
            dot.dot(cfg, df, True, True)

        #newb = Switch(cfg.node(swstart).get('val'), cond.expr.args[0], ncases, False)
        #cfg.add_node(swstart, val=newb)
        #for n in search_nodes:
        #    if n != swstart:
        #        cfg.remove_node(n)
        #for n in leaf_nodes:
        #    cfg.remove_node(n)
        #cfg.add_edge(swstart, def_nodes[0])
        return True


def match_if(cfg):
    for v, _ in cfg.iter_nodes():
        if cfg.degree_out(v) == 2:
            a, b = cfg.sorted_succ(v)

            if cfg.degree_in(a) >= 2 and cfg.degree_in(b) == 1 and cfg.degree_out(b) == 1:
                truth = False
                cond = cfg.edge(v, a).get("cond")
            elif cfg.degree_in(b) >= 2 and cfg.degree_in(a) == 1 and cfg.degree_out(a) == 1:
                truth = True
                cond = cfg.edge(v, a).get("cond")
                a, b = b, a
            else:
                continue

            c = cfg.succ(b)[0]
            if c == a:
                log.info("if: %s, %s, %s", v, b, c)
                v = split_bblock(cfg, v)
                if_header = cfg.node(v)["val"]
                t_block = cfg.node(b)["val"]
                if truth == False:
                    cond = cond.neg()
                newb = IfElse(if_header, t_block, None, cond)
                cfg.add_node(v, val=newb)
                cfg.remove_node(b)
                cfg.set_edge(v, a, cond=None)
                return True


IFELSE_COND = 0
IFELSE_BRANCH = 1

class IfElse(RecursiveBlock):
    def __init__(self, header, t_block, f_block, true_cond):
        super().__init__(header.addr)
        self.header = header
        self.branches = [(true_cond, t_block), (None, f_block)]

    def subblocks(self):
        return [x[1] for x in self.branches if x[1]]

    def recursive_union(self, func):
        res = set()
        for cond, subb in self.branches:
            if cond:
                res |= func(cond)
            if subb:
                res |= func(subb)
        return res

    def swap_branches(self):
        # Swap If/Else branches, negating condition
        assert len(self.branches) == 2
        assert self.branches[1][1] is not None
        [(true_cond, t_block), (dummy, f_block)] = self.branches
        self.branches = [(true_cond.neg(), f_block), (None, t_block)]

    def __repr__(self):
        return "%s(%r)" % (self.__class__.__name__, self.branches)

    def dump(self, stream, indent=0, printer=str):
        self.write(stream, indent, "if %s {" % self.branches[0][0])
        self.branches[0][1].dump(stream, indent + 1, printer)

        for cond, block in self.branches[1:-1]:
            self.write(stream, indent, "} else if %s {" % cond)
            block.dump(stream, indent + 1, printer)

        assert self.branches[-1][0] is None
        if self.branches[-1][1] is not None:
            self.write(stream, indent, "} else {")
            self.branches[-1][1].dump(stream, indent + 1, printer)
        self.write(stream, indent, "}")


# if (!(a > b)) goto false
# {true}
# goto out
# false:
# {false}
# out:

def match_ifelse(cfg):
    for v, _ in cfg.iter_nodes():
        if cfg.degree_out(v) == 2:
            succ = cfg.sorted_succ(v)
            cond = cfg.edge(v, succ[0]).get("cond")
            if cond:
                f_v = succ[0]
                t_v = succ[1]
                f_v_s = cfg.succ(f_v)
                t_v_s = cfg.succ(t_v)

                if len(t_v_s) != 1: continue
                if len(f_v_s) != 1: continue
                common = list(set(t_v_s) & set(f_v_s))
                if common:
                    f_v_s = common

                    log.info("ifelse: %s, %s, %s, %s", v, t_v, f_v, f_v_s[0])
                    v = split_bblock(cfg, v)
                    if_header = cfg.node(v)["val"]
                    t_block = cfg.node(t_v)["val"]
                    f_block = cfg.node(f_v)["val"]
                    newb = IfElse(if_header, t_block, f_block, cond.neg())
                    cfg.add_node(v, val=newb)
                    cfg.remove_node(t_v)
                    cfg.remove_node(f_v)
                    cfg.add_edge(v, f_v_s[0])
                    return True


#
# If we have:
#
# if (cond) {
#   if ...
# } else {
#   // not if
# }
#
# It's better to transform it to:
#
# if (!cond) {
#   // not if
# } else {
#   if ...
# }
#
# , then to be recognized by match_if_else_ladder

def match_if_else_inv_ladder_recursive(block):
    if isinstance(block, IfElse):
        if len(block.branches) != 2:
            log.warn("match_if_else_inv_ladder: Must be applied before match_if_else_ladder")
            return
        if_block = block.branches[0][IFELSE_BRANCH]
        else_block = block.branches[1][IFELSE_BRANCH]
        if isinstance(if_block, IfElse) and not isinstance(else_block, IfElse):
            block.swap_branches()
        if_block = block.branches[0][IFELSE_BRANCH]
        else_block = block.branches[1][IFELSE_BRANCH]
        match_if_else_inv_ladder_recursive(if_block)
        match_if_else_inv_ladder_recursive(else_block)

def match_if_else_inv_ladder(cfg):
    for v, node_props in cfg.iter_nodes():
        block = node_props["val"]
        match_if_else_inv_ladder_recursive(block)


#
# If we have:
#
# $a0 = val1
# if (...) {
#   $a0 = val2
# }
#
# it's equivalent to:
#
# if (...) {
#   $a0 = val2
# } else {
#   $a0 = val1
# }
#
# And transforming it to such may enable match_if_else_ladder
def match_if_else_unjumped(cfg):
    for v, node_props in cfg.iter_nodes():
        #print((v, node_props))
        block = node_props["val"]
        if type(block) is BBlock and cfg.degree_out(v) == 1:
            succ = cfg.succ(v)[0]
            #print(">", (succ, cfg.node(succ)))
            succ_block = cfg.node(succ)["val"]
            if isinstance(succ_block, IfElse) \
              and succ_block.branches[-1][IFELSE_BRANCH] is None \
              and type(succ_block.branches[0][IFELSE_BRANCH]) is BBlock:
                first_defs = block.defs(regs_only=False)
                second_defs = succ_block.defs(regs_only=False)
                second_uses = succ_block.uses()
                log.info("ifelse_unjumped: first: defs: %s | second: defs: %s, uses: %s", first_defs, second_defs, second_uses)
                if not first_defs:
                    # Everything was apparently DCEed
                    return
                if not first_defs.issubset(second_defs):
                    log.info("ifelse_unjumped: can't apply, because first defines more other vars than 2nd: %s vs %s",
                         first_defs, second_defs)
                    return
                if first_defs & second_uses:
                    log.info("ifelse_unjumped: can't apply, because if uses (%s) vals defined in preceding block (%s)",
                        second_uses, first_defs)
                    return
                # TODO: Are the checks above enough?
                log.info("ifelse_unjumped: %s, %s", v, succ)
                cfgutils.detach_node(cfg, v)
                succ_block.branches[-1] = (None, block)
                return True


def match_if_else_ladder(cfg):
    for v, node_props in cfg.iter_nodes():
        block = node_props["val"]
        if isinstance(block, IfElse):
            else_block = block.branches[-1][1]
            if isinstance(else_block, IfElse):
                block.branches = block.branches[:-1] + else_block.branches
                return True


class Loop(RecursiveBlock):
    def __init__(self, b):
        super().__init__(b.addr)
        self.items = [b]

    def subblocks(self):
        return self.items

    def __repr__(self):
        return "%s(%s)" % (self.__class__.__name__, self.items[0])

    def dump(self, stream, indent=0, printer=str):
        self.write(stream, indent, "while (1) {")
        for b in self.items:
            b.dump(stream, indent + 1, printer)
        self.write(stream, indent, "}")


def match_infloop(cfg):
    for v, _ in cfg.iter_nodes():
        if cfg.degree_out(v) == 1:
            for s in cfg.succ(v):
                if s == v:
                    log.info("infloop: %s", v)
                    b = cfg.node(v)["val"]
                    newb = Loop(b)
                    cfg.add_node(v, val=newb)
                    cfg.remove_edge(v, v)
                    return True


class DoWhile(RecursiveBlock):
    def __init__(self, b, cond):
        super().__init__(b.addr)
        self.cond = cond
        self.items = [b]

    def subblocks(self):
        return self.items

    def __repr__(self):
        return "%s(%s)" % (self.__class__.__name__, self.items[0])

    def dump(self, stream, indent=0, printer=str):
        self.write(stream, indent, "do {")
        for b in self.items:
            b.dump(stream, indent + 1, printer)
        self.write(stream, indent, "} while %s;" % self.cond)


def match_dowhile(cfg):
    for v, _ in cfg.iter_nodes():
        if cfg.degree_out(v) == 2:
            for s in cfg.succ(v):
                if s == v:
                    log.info("dowhile: %s", v)
                    b = cfg.node(v)["val"]
                    newb = DoWhile(b, cfg.edge(v, v).get("cond"))
                    cfg.add_node(v, val=newb)
                    cfg.remove_edge(v, v)
                    return True


class While(RecursiveBlock):
    def __init__(self, b, cond):
        super().__init__(b.addr)
        self.cond = cond
        self.items = [b]

    def subblocks(self):
        return self.items

    def __repr__(self):
        return "%s(%s)" % (self.__class__.__name__, self.items[0])

    def dump(self, stream, indent=0, printer=str):
        self.write(stream, indent, "while %s {" % self.cond)
        for b in self.items:
            b.dump(stream, indent + 1, printer)
        self.write(stream, indent, "}")


def match_while(cfg):
    for v, _ in cfg.iter_nodes():
        if cfg.degree_out(v) == 2:
            succ = cfg.sorted_succ(v)
            back_cand = cfg.succ(succ[0])
            if len(back_cand) == 1 and back_cand[0] == v and cfg.degree_in(succ[0]) == 1:
                log.info("while: %s, %s", v, succ[0])
                b = cfg.node(succ[0])["val"]
                newb = While(b, cfg.edge(v, succ[0]).get("cond"))
                cfg.add_node(v, val=newb)
                cfg.remove_node(succ[0])
                return True

#
# if (cond) {
#   do {...} while (cond);
# }
#
# =>
#
# while (cond) {...}
#
def match_if_dowhile(cfg):
    for addr, info in cfg.iter_nodes():
        bblock = info["val"]
        if type(bblock) is IfElse:
            subs = bblock.subblocks()
            if len(subs) == 1 and type(subs[0]) is DoWhile:
                if_cond = bblock.branches[0][0]
                dowhile_cond = subs[0].cond
                #print(if_cond, if_cond == dowhile_cond)
                if if_cond != dowhile_cond:
                    continue
                while_bb = While(subs[0].items[0], if_cond)
                info["val"] = while_bb
                return True


class ControlAnd(BBlock):
    def __init__(self, addr, cond1, cond2):
        super().__init__(addr)
        #print((addr, cond1, cond2))
        self.cond = CompoundCond(cond1.list() + ["||"] + cond2.list())
        self.l = []

    def __repr__(self):
        return "%s(%s)" % (self.__class__.__name__, self.cond)

    def dump(self, stream, indent=0, printer=str):
        self.write(stream, indent, "/* && */")


def match_control_and(cfg):
    for v, _ in cfg.iter_nodes():
        if cfg.degree_out(v) == 2:
            succ1 = cfg.sorted_succ(v)
            v2 = succ1[1]
            if cfg.degree_out(v2) == 2:
                succ2 = cfg.sorted_succ(v2)
                assert len(succ2) == 2
                if succ1[0] == succ2[0]:
                    log.info("and %s, %s", v, v2)
                    newb = ControlAnd(v, cfg.edge(v, succ1[0]).get("cond"), cfg.edge(v2, succ1[0]).get("cond"))
                    cfg.add_node(v, val=newb)
                    cfg.set_edge(v, succ1[0], cond=newb.cond)
                    cfg.remove_node(v2)
                    cfg.add_edge(v, succ2[1])
                    return True


def match_abnormal_sel(cfg):
    """Should be run only if match_if, match_ifelse don't match anything
    in acyclic graph. Then any join node belong to abnormal selection
    pattern. We try to find the top-most and split it, after which normal
    structured matches should be tried again.
    """
    for v, _ in cfg.iter_rev_postorder():
        if cfg.degree_in(v) == 2 and cfg.degree_out(v) == 1:
            split_node(cfg, v)
            return True
