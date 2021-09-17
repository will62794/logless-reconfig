#
# TLC runner script.
#

default_config = {
    "INIT": "Init",
    "NEXT": "Next",
    "CONSTANT": {
        "Nil" : "Nil",
        "Server" : "{n1,n2,n3}",
        "Secondary" : "Secondary",
        "Primary" : "Primary",
        "MaxLogLen" : "2",
        "MaxTerm" : "3",
        "MaxConfigVersion" : "3",
        "n1" : "n1",
        "n2" : "n2",
        "n3" : "n3",
        "NumRandSubsets": "10"
    },
    "SYMMETRY": "Symmetry",
    "CONSTRAINT": "StateConstraint",
    "INVARIANT": ["OnePrimaryPerTerm"]
}

def write_config(config_obj, fname):
    """ Write TLC config given in 'config_obj' to the file specified by 'fname'.""" 

    cf = open(fname, "w")
    for key in config_obj:
        if key == "CONSTANT":
            cf.write("CONSTANTS\n")
            for ck in config_obj[key]:
                cf.write("%s = %s" % (ck,str(config_obj[key][ck])))
                cf.write("\n")
        elif key == "INVARIANT":
            for inv in config_obj[key]:
                cf.write("INVARIANT %s" % inv)
                cf.write("\n")
        else:
            cf.write("%s %s" % (key,str(config_obj[key])))
            cf.write("\n")
    cf.close()

def run_one_params(invariant, config, tlc_workers):
    """ Check the given invariant for a single parameter configuration using TLC. """

    # Set constants.
    # for i,param_val in enumerate(param_vals):
    #     config["CONSTANT"][param_names[i]] = param_val 

    # Set invariant.
    config["INVARIANT"] = [invariant]
    
    cfg_filename = tmp_models_dir + "/Merger-params_" + pstr + ".cfg"
    write_config(config, cfg_filename)

    tlc_cmd = "java -cp tla2tools.jar tlc2.TLC -workers %d -deadlock -config %s %s" % (tlc_workers, cfg_filename, specname)
    # print(tlc_cmd)
    proc = subprocess.Popen(tlc_cmd, stdout=subprocess.PIPE, shell=True)
    stdout_value = proc.communicate()[0]
    lines =  [str(l) for l in stdout_value.splitlines()]
    # for l in lines:
        # print(l)

    # Check for success or invariant violation.
    noerror = any([re.match(".*No error has been found", str(l)) for l in lines])
    inv_violation = any([re.match(".*Invariant.*is violated", l) for l in lines])
    assert noerror != inv_violation
    return noerror

if __name__ == "__main__":
    write_config(default_config, "model.cfg")