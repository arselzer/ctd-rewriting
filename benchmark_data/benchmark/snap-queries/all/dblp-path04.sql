select count(*) from dblp p1, dblp p2, dblp p3, dblp p4, dblp p5 where p1.toNode = p2.fromNode AND p2.toNode = p3.fromNode AND p3.toNode = p4.fromNode AND p4.toNode = p5.fromNode
