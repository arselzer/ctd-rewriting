
from ctdcheck import CTDCheck
from hypergraph import HyperGraph
from functools import partial
from ctdcheck import Block
from ctdcheck import VertSet


def all_choose_k(S, k):
    from itertools import chain, combinations
    return chain(*(combinations(S, kp) for kp in range(1,k+1)))
#
def all_lambdas(E, k):
    for es in all_choose_k(E, k):
        yield set.union(*es)

# (over approximates) the bags produced by the LogK algorithm
def computesoftk(h, k):
    softk = list()
    for P in all_lambdas(h.E,k):
        for C in h.separate(P, only_vertices=True):
            for L in all_lambdas(h.E, k):
                B = set.intersection(C, L)
                if len(B) > 1 and B not in softk:
                    softk.append(B)
    return softk
    
# computes the blocks of a bag by computing its components w.r.t. h
def bag_to_blocks(h,B):  
    blocks = list()
    for C in h.separate(B, only_vertices=True):
        blocks.append(Block(VertSet(B),VertSet(C)))
    blocks.append(Block(VertSet(B),VertSet(set())))  # adding trivial block too
    return blocks


# computes the blocks of a bag by computing its components w.r.t. h
def bag_to_blocksConnected(h,B):  
    blocks = list()
    for C in h.separate(B, only_vertices=True):
        tempBlock = Block(VertSet(B),VertSet(C))
        if tempBlock.connected(h):
            blocks.append(tempBlock)
    blocks.append(Block(VertSet(B),VertSet(set())))  # adding trivial block too
    return blocks


# Same as  computeosftK, but returns directly the blocks
def computesoftkBlocks(h, k):
    out = list()
    listOfLists = map(partial(bag_to_blocks,h),computesoftk(h,k))
    for ll in listOfLists:
        for l in ll:
            out.append(l)
    return out


# Same as  computeosftK, but returns directly the blocks
def computesoftkBlocksConnected(h, k):
    out = list()
    listOfLists = map(partial(bag_to_blocksConnected,h),computesoftk(h,k))
    for ll in listOfLists:
        for l in ll:
            out.append(l)
    return out



h = HyperGraph.fromHyperbench("/home/okulmus/Documents/OldBenchmarks/benchmark/hyperbench/1.dtl")

ctd = CTDCheck(h)

blocks = computesoftkBlocksConnected(h,2)

for b in blocks:
    print("Adding blocks ", b)
    ctd.addBlock(b)
    # headedBy = ctd.head_to_blocks[repr(b.head)]
    # print("All blocks headed by ",b.head )
    # for h in headedBy:
        # print(h)


print("Done adding blocks")

print("Running hasDecomp")

res = ctd.hasDecomp()

print("hasDecomp done. Result: ",res)