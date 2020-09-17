import graphviz

f = open("LoglessReconfig.toolbox/Reconfig/graphs.txt")
items = f.read().splitlines()

items = items[100:]
dot = graphviz.Digraph(comment='The Round Table')
dot.graph_attr['rankdir'] = 'LR'

reconfig_graphs = set()

# Build the unique reconfig graphs.
for k,line in enumerate(items):
    line = line.strip().replace("{", "").replace("}", "")
    edges = line.replace("\"", "").split(",")
    edges = tuple([e.strip() for e in edges])
    # print edges
    reconfig_graphs.add(edges)

for k,rc in enumerate(reconfig_graphs):
    for edge in rc:
        print e
        n1, n2 = (edge.split("->")[0].strip(), edge.split("->")[1].strip())
        dot.node(str(k)+n1, label=n1)
        dot.node(str(k)+n2, label=n2)
        dot.edge(str(k)+n1, str(k)+n2)
    # dot += "}"
    # print k, dot

# dot.render('graphs/config-graph-' + str(k) + '.gv', view=False)
dot.render('graphs/config-graph-FULL' + '.gv', view=False)




    # i.strip().replace("<<", "").replace(">>", "").replace("{", "").replace("}", "")
    # elems = [e for e in i.split(",")]
    # elems = [e.replace("{", "").replace("}", "").strip() for e in elems]
    # config = elems[0]
    # configVersionOld  = elems[1]
    # configTermOld = elems[2]
    # print (config, configVersionOld, configTermOld)

