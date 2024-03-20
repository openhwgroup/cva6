# Import all schema classes for implementation-defined behavior list.
from schemas.impl_file import *

# Import the 'variconf' package.
import variconf

# Create a configuration handler object for CV32A65X.
cv32a65x_conf = variconf.WConf(ImplSpecificBehaviors)

# Load the 'bootstrapped' descrition of impl-defined behaviors in RV ISA spec vol. 2
# (result of programmaticvally adding missing tags to the original file '..../implement.yaml').
cv32a65x_conf.load_file('spec_inventory/vol2priv/implement-bootstrapped.yaml')

# Print entry #15 of the 'behaviors' list as internal object (a dictionary).
behavior_15 = cv32a65x_conf.get().behaviors[15]
print(behavior_15)

# For the following operation we need OmegaConf class methods...
from omegaconf import OmegaConf

# Print Yaml representation of behavior #15.
print(OmegaConf.to_yaml(behavior_15))

# Print the relevance reason of behavior #15.
print("Behavior #15 is %srelevant because it %s" %
      ("" if behavior_15.relevant else "not ", behavior_15.relevant_why))
