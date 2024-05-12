Any Custom CSR
--------------

All custom CSRs follow the same schema as an architecture-defined CSR.

uArch signals
-------------

    - **^uarch_ signal/group name**

        All signal or group names must contain the ``uarch_`` prefix.

    - **msb**

        An integer value indicating the msb position of the signal.

    - **lsb**

        An integer indicating the lsb position of the group.

    - **reset-val**

        An integer indicating the reset value of a signal/group.
        In case of a group, this value resides outside the subfields dict.

    - **legal**

        A list of legal values for this signal.

    - **subfields**
    
        An optional way to structure signals. A subfield would contain msb, lsb, legal fields.

