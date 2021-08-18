import fileinput
import json

def parse_tlc_lines():
    lines = []
    states = []
    for line in fileinput.input():
        if "jsonstr" in line:
            tokens = line.split("=")
            json_val = tokens[1].strip()[1:-1].decode("string_escape")
            json_state = json.loads(json_val)
            states.append(json_state)
            # print json_state
            # print line
    return states

tikz_templ = """
\\begin{tikzpicture}
    \\footnotesize

    % Circle node with text annotation.
    \\filldraw[black] (0,0) circle (2pt) node[anchor=west] {$n_1 (1,0)$};
    \\filldraw[black] (0,1) circle (2pt) node[anchor=west] {$n_2 (1,0)$};
    \\filldraw[black] (0,2) circle (2pt) node[anchor=west] {$n_3 (1,0)$};
    
\end{tikzpicture}
"""

def subscriptize(sid):
    return sid[0] + "_" + sid[1]

def latex_set_str(lst):
    return "\{" + ",".join(map(subscriptize, lst)) + "\}"

def make_tikz_state(si,state):
    out_str = "\\begin{tikzpicture}\n"
    out_str += "\\footnotesize\n"
    servers = state.values()[0].keys()
    for ind,ni in enumerate(reversed(servers)):
        nstr = "\\filldraw[black] (0,%d) node[anchor=west] {$%s$};\n"
        nistr = subscriptize(ni) + " : "
        if si > 0:
            nistr = ""
        textcolor = "black"
        if state["state"][ni] == "Primary":
            textcolor = "blue"
        log = ""
        if "log" in state:
            log = state["log"][ni]
        configAndLog = "\underset{%s}{%s}" % (log, latex_set_str(state["config"][ni]))
        stateStr = state["state"][ni][0]
        stateSymbol = ""
        if stateStr == "P":
            # Add symbol for primary server.
            stateSymbol = "\\symqueen"
        args = (textcolor,nistr,configAndLog,stateStr,state["currentTerm"][ni],state["configVersion"][ni],state["configTerm"][ni],stateSymbol)
        valstr = "\\textcolor{%s}{%s\\underset{%s}{%s^%s_{(%s,%s) %s} }}" % args
        out_str += (nstr % (ind, valstr))
    out_str += "\\end{tikzpicture}"
    return out_str

def make_tikz_states(states):
    return [make_tikz_state(si, s) for (si,s) in enumerate(states)]

# Parse the trace into a list of states.
states = parse_tlc_lines()
# print states[0].keys()
tikz = make_tikz_states(states)

for t in tikz:
    print t
    # print "$\\rightarrow$"
    print "\\vline"