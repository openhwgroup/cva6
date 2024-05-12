import logging
import argparse
import operator

import ruamel
from ruamel.yaml import YAML
import yaml as pyyaml

def hexint_presenter(dumper, data):
    return dumper.represent_int(hex(data))

class NoAliasDumper(pyyaml.Dumper):
    def ignore_aliases(self, data):
        return True


def dump_yaml(foo, outfile, no_anchors=False):
    if no_anchors:
        pyyaml.add_representer(int, hexint_presenter)
        pyyaml.dump(foo, outfile, Dumper=NoAliasDumper)
    else:
        yaml = YAML(typ="rt")
        yaml.default_flow_style = False
        yaml.allow_unicode = True
        yaml.compact(seq_seq=False, seq_map=False)
        yaml.indent = 4
        yaml.block_seq_indent = 2
        yaml.dump(foo, outfile)


def load_yaml(foo, no_anchors=False):

    if no_anchors:
        yaml = YAML(typ="safe")
    else:
        yaml = YAML(typ="rt")
    yaml.default_flow_style = False
    yaml.allow_unicode = True
    yaml.compact(seq_seq=False, seq_map=False)
    yaml.indent = 4
    yaml.block_seq_indent = 2

    try:
        with open(foo, "r") as file:
            return yaml.load(file)
    except ruamel.yaml.constructor.DuplicateKeyError as msg:
        logger = logging.getLogger(__name__)
        error = "\n".join(str(msg).split("\n")[2:-7])
        logger.error(error)
        raise SystemExit


class ColoredFormatter(logging.Formatter):
    """
        Class to create a log output which is colored based on level.
    """

    def __init__(self, *args, **kwargs):
        super(ColoredFormatter, self).__init__(*args, **kwargs)
        self.colors = {
            'DEBUG': '\033[94m',
            'INFO': '\033[92m',
            'WARNING': '\033[93m',
            'ERROR': '\033[91m',
        }

        self.reset = '\033[0m'

    def format(self, record):
        msg = str(record.msg)
        level_name = str(record.levelname)
        name = str(record.name)
        color_prefix = self.colors[level_name]
        return '{0}{1:<9s} {4}: {2}{3}'.format(color_prefix,
                                            '[' + level_name + ']', msg,
                                            self.reset, name)


def setup_logging(log_level):
    """Setup logging

        Verbosity decided on user input

        :param log_level: User defined log level

        :type log_level: str
    """
    numeric_level = getattr(logging, log_level.upper(), None)

    if not isinstance(numeric_level, int):
        print(
            "\033[91mInvalid log level passed. Please select from debug | info | warning | error\033[0m"
        )
        raise ValueError("{}-Invalid log level.".format(log_level))

    logging.basicConfig(level=numeric_level)


class SortingHelpFormatter(argparse.HelpFormatter):

    def add_arguments(self, actions):
        actions = sorted(actions, key=operator.attrgetter('option_strings'))
        super(SortingHelpFormatter, self).add_arguments(actions)


def riscv_config_cmdline_args():
    parser = argparse.ArgumentParser(
        formatter_class=SortingHelpFormatter,
        prog="riscv_config",
        description="RISC-V Configuration Validator")
    parser.add_argument('--version',
                        '-v',
                        help='Print version of RISCV-CONFIG being used',
                        action='store_true')
    parser.add_argument('--isa_spec',
                        '-ispec',
                        type=str,
                        metavar='YAML',
                        default=None,
                        help='The YAML which contains the ISA specs.')
    parser.add_argument('--platform_spec',
                        '-pspec',
                        type=str,
                        metavar='YAML',
                        default=None,
                        help='The YAML which contains the Platfrorm specs.')
    parser.add_argument('--debug_spec',
                        '-dspec',
                        type=str,
                        metavar='YAML',
                        default=None,
                        help='The YAML which contains the debug csr specs.') 
    parser.add_argument('--custom_spec',
                        '-cspec',
                        type=str,
                        metavar='YAML',
                        default=None,
                        help='The YAML which contains the custom csr specs.')                        
    parser.add_argument(
        '--work_dir',
        type=str,
        default="riscv_config_work",
        metavar='DIR',
        help='The name of the work dir to dump the output files to.')
    parser.add_argument('--verbose',
                        action='store',
                        default='info',
                        help='debug | info | warning | error',
                        metavar="")
    parser.add_argument('--no_anchors',
                        action='store_true',
                        help='Unroll/Disable all anchors')
    return parser

def pretty_print_yaml(yaml):
    res = ''''''
    for line in ruamel.yaml.round_trip_dump(yaml, indent=5, block_seq_indent=3).splitlines(True):
        res += line
    return res

