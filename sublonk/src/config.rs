// pub(crate) const POW_NUM_WITNESS_CIRCUIT: usize = 10;
// pub(crate) const NUM_WITNESS_CIRCUITS: usize = 1 << POW_NUM_WITNESS_CIRCUIT;
pub(crate) const POW_SEGMENT_SIZE: usize = 6;
pub(crate) const SEGMENT_SIZE: usize = 1 << POW_SEGMENT_SIZE;
// pub(crate) const POW_WITNESS_SIZE: usize = POW_NUM_WITNESS_CIRCUIT + POW_SEGMENT_SIZE;
// pub(crate) const WITNESS_SIZE: usize = 1 << POW_WITNESS_SIZE;
pub(crate) const NUM_UNUSABLE_ROWS: usize = SEGMENT_SIZE;
// pub(crate) const USABLE_WITNESSES_SIZE: usize = WITNESS_SIZE - NUM_UNUSABLE_ROWS;
// pub(crate) const VALID_NUM_WITNESS_CIRCUITS: usize = NUM_WITNESS_CIRCUITS - 1;

pub(crate) const POW_NUM_TABLE_CIRCUIT: usize = 10;
pub(crate) const NUM_TABLE_CIRCUITS: usize = 1 << POW_NUM_TABLE_CIRCUIT;

pub(crate) struct Config {
    pub(crate) pow_num_witness_circuits: usize,
    pub(crate) num_witness_circuits: usize,
    pub(crate) pow_segment_size: usize,
    pub(crate) segment_size: usize,
    pub(crate) pow_witness_size: usize,
    pub(crate) witness_size: usize,
    pub(crate) num_unusable_rows: usize,
    pub(crate) usable_witnesses_size: usize,
    pub(crate) valid_num_witness_circuits: usize,
    pub(crate) pow_num_table_circuit: usize,
    pub(crate) num_table_circuits: usize,
    pub(crate) num_different_segments: usize,
}