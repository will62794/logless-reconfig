import graphviz, sys

filepath = sys.argv[1]
f = open(filepath)
lines = f.read().splitlines()

# lines = lines[200:-90]
lines = lines[0:]
print lines
dot = graphviz.Digraph(comment='The Round Table')
dot.graph_attr['rankdir'] = 'LR'

reconfig_graphs = list()

# Build the unique reconfig graphs.
last_edges = None
reconfig_graphs.append((None, None))
for k,line in enumerate(lines):
    # Skip lines containing committec configs.
    if k % 2 == 1:
        continue
    if len(line)<2 or not (line[0]=="{" and line[-1]=="}"):
        print "Skipping line: ", line
        continue
    # print line
    if line == "{}":
        if len(reconfig_graphs)>0 and reconfig_graphs[-1]: 
            # reconfig_graphs.append(None)
            reconfig_graphs.append((None,None))
    else:
        print "raw:",line
        cleaned_line = line.replace("n1, ", "n1-")
        cleaned_line = cleaned_line.replace("n2, ", "n2-")
        cleaned_line = cleaned_line.replace("n3, ", "n3-")
        cleaned_line = cleaned_line.replace("n4, ", "n4-")
        cleaned_line = cleaned_line.replace("n5, ", "n5-")
        cleaned_line = cleaned_line.strip().replace("{", "").replace("}", "").replace("\"", "")

        committed_configs_line = lines[k+1]
        committed_configs_cleaned_line = committed_configs_line.strip().replace("{", "").replace("}", "").replace("\"", "")
        committed_configs = committed_configs_cleaned_line.split(",")
        committed_configs = tuple([c.strip() for c in committed_configs])

        print "committed:", committed_configs
        print "cleaned:",cleaned_line
        edges = cleaned_line.split(",")
        edges = tuple([e.strip() for e in edges])
        print edges
        def parse_edge(e):
            nodes = e.split("->")
            return (nodes[0].strip(), nodes[1].strip())
        edges = tuple(map(parse_edge, edges))
        print edges
        if last_edges and last_edges != edges:
            reconfig_graphs.append((edges, committed_configs))
        last_edges = edges
reconfig_graphs.append((None, None))
reconfig_graphs = set(reconfig_graphs)

# reconfig_graphs = sorted(reconfig_graphs, key = lambda rc : len(rc), reverse=True)
# reconfig_graphs = reversed(reconfig_graphs)

print "*** Generating reconfig Digraph ***"
subgraphid = 0
curr_subgraph = graphviz.Digraph(comment='cluster')
curr_subgraph.graph_attr['rankdir'] = 'LR'
for k,rcpair in enumerate(reconfig_graphs):
    rc,committed_configs = rcpair
    if rc is None:
        # delineate new graph.
        curr_subgraph.attr('node', color='orange')
        curr_subgraph.node("delimiter" + str(k), label="delimiter" + str(k))
        # start a new subgraph.
        subgraphid += 1
        dot.subgraph(curr_subgraph)
        curr_subgraph = graphviz.Digraph(comment='cluster' + str(subgraphid))
    else:
        print rc,committed_configs
        for edge in rc:
            n1, n2 = (edge)
            curr_subgraph.node(str(k)+n1, label=n1)

            nodecolor = "red" if n2 in committed_configs else "white"

            # An election edge.
            if n1[1] != n2[1]:
                # curr_subgraph.attr('node', fillcolor='lightblue', style="filled")
                curr_subgraph.attr('edge', color='orange', style="filled", penwidth="1")
                curr_subgraph.node(str(k)+n2, label=n2,shape="rectangle")
            else:
                curr_subgraph.node(str(k)+n2, label=n2,shape="circle", style="filled", fillcolor=nodecolor)

            curr_subgraph.edge(str(k)+n1, str(k)+n2)
            # curr_subgraph.attr('node', fillcolor='none', style="filled")
            curr_subgraph.attr('edge', color='black', penwidth="1")

# dot.render('graphs/config-graph-' + str(k) + '.gv', view=False)
dot.render('graphs/config-graph-FULL' + '.gv', view=False)