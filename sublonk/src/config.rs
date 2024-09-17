pub(crate) const POW_NUM_WITNESS_CIRCUIT: usize = 10;
pub(crate) const NUM_WITNESS_CIRCUITS: usize = 1 << POW_NUM_WITNESS_CIRCUIT;
pub(crate) const POW_SEGMENT_SIZE: usize = 6;
pub(crate) const SEGMENT_SIZE: usize = 1 << POW_SEGMENT_SIZE;
pub(crate) const POW_WITNESS_SIZE: usize = POW_NUM_WITNESS_CIRCUIT + POW_SEGMENT_SIZE;
pub(crate) const WITNESS_SIZE: usize = 1 << POW_WITNESS_SIZE;
pub(crate) const NUM_UNUSABLE_ROWS: usize = SEGMENT_SIZE;
pub(crate) const USABLE_WITNESSES_SIZE: usize = WITNESS_SIZE - NUM_UNUSABLE_ROWS;

pub(crate) const VALID_NUM_WITNESS_CIRCUITS: usize = NUM_WITNESS_CIRCUITS - 1;
