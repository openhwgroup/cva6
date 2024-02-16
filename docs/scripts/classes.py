# Copyright 2024 Thales DIS France SAS
#
# Licensed under the Solderpad Hardware License, Version 2.1 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Original Author: Jean-Roch COULON - Thales

#!/usr/bin/python3


class Parameter:
    def __init__(
        self,
        datatype,
        description,
        value,
    ):
        self.datatype = datatype
        self.description = description
        self.value = value


class PortIO:
    def __init__(
        self,
        name,
        direction,
        data_type,
        description,
        connexion,
    ):
        self.name = name
        self.direction = direction
        self.data_type = data_type
        self.description = description
        self.connexion = connexion
