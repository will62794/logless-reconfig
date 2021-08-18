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

#
# \begin{center}
#   \begin{tabular}{ l | c | r }
#     \hline
#     1 & 2 & 3 \\ \hline
#     4 & 5 & 6 \\ \hline
#     7 & 8 & 9 \\
#     \hline
#   \end{tabular}
# \end{center}
#

def make_latex_state_table(rows):
    nrows = len(rows)
    ncols = 1 + len(rows[0]) # account for server identifier column.
    colstr = "|".join((["c"] * ncols))
    table = "\\begin{tabular}{%s}\n" % colstr
    rowstrs = []
    state_header_row = [""]
    for col in range(1,ncols):
        state_header_row.append("$%d$" % col)

    table += " & ".join(state_header_row)
    table += "\\\\ \hline \n\n"
    for rowi,row in enumerate(rows):
        # Append server identifier.
        row = ["$n_%d$" % rowi] + row
        rowstrs.append(" & ".join(row))
    # table += "\\\\\n \\hline\n\n".join(rowstrs)
    table += "\\\\\n \n\n".join(rowstrs)
    table += "\n"
    table += "\\end{tabular}\n"
    return table

def subscriptize(sid):
    return sid[0] + "_" + sid[1]

def latex_set_str(lst):
    return "\{" + ",".join(map(subscriptize, lst)) + "\}"

def make_server_latex(state, ni):
    # nstr = "\\filldraw[black] (0,%d) node[anchor=west] {$%s$};\n"
    # nstr = "%s"
    ind = 0
    # nistr = subscriptize(ni) + " : "
    # if si > 0:
    nistr = ""
    out_str = ""
    textcolor = "black"
    if state["state"][ni] == "Primary":
        textcolor = "black"
    log = ""
    if "log" in state:
        log = state["log"][ni]
    configAndLog = "\underset{%s}{%s}" % (log, latex_set_str(state["config"][ni]))
    stateStr = state["state"][ni][0]
    stateSymbol = ""
    if stateStr == "P":
        # Add symbol for primary server.
        stateSymbol = "\\textcolor{blue}{\\symqueen}"
    # args = (textcolor,nistr,configAndLog,stateStr,state["currentTerm"][ni],stateSymbol, state["configVersion"][ni],state["configTerm"][ni])
    args = (nistr,configAndLog,stateStr,state["currentTerm"][ni],stateSymbol, state["configVersion"][ni],state["configTerm"][ni])
    valstr = "%s\\underset{%s}{%s^{%s \, %s}_{(%s,%s)}}" % args
    # out_str += (nstr % (ind, valstr))
    # out_str += nstr #% (valstr))
    return "$" + valstr + "$"
    # return out_str

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
            textcolor = "black"
        log = ""
        if "log" in state:
            log = state["log"][ni]
        configAndLog = "\underset{%s}{%s}" % (log, latex_set_str(state["config"][ni]))
        stateStr = state["state"][ni][0]
        stateSymbol = ""
        if stateStr == "P":
            # Add symbol for primary server.
            stateSymbol = "\\textcolor{blue}{\\symqueen}"
        args = (textcolor,nistr,configAndLog,stateStr,state["currentTerm"][ni],stateSymbol, state["configVersion"][ni],state["configTerm"][ni])
        valstr = "\\textcolor{%s}{%s\\underset{%s}{%s^{%s \, %s}_{(%s,%s)} }}" % args
        out_str += (nstr % (ind, valstr))
    out_str += "\\end{tikzpicture}"
    return out_str

def make_tikz_states(states):
    trace_rows = []
    servers = states[0].values()[0].keys()
    for ind,ni in enumerate(servers):
        row = []
        for (si,s) in enumerate(states):
            server_latex = make_server_latex(s,ni)
            # print server_latex
            # In the last state (the bad state), highlight the cell red.
            if si + 1 == len(states):
                server_latex = "\\cellcolor{red!10}" + server_latex
            row.append(server_latex)
        trace_rows.append(row)
    # print len(trace_rows)
    return make_latex_state_table(trace_rows)

# Parse the trace into a list of states.
states = parse_tlc_lines()
# print states[0].keys()
tikz = make_tikz_states(states)

print tikz