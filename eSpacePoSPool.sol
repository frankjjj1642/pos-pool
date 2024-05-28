//File： fs://7c47ba1df1e64c71b8fa8ad04710aaa3/contracts/interfaces/IPoSPool.sol
//SPDX-License-Identifier: Unlicense
pragma solidity ^0.8.0;




interface IPoSPool {
  struct PoolSummary {
    uint256 available;
    uint256 interest;
    uint256 totalInterest; // total interest of all pools
  }

  struct UserSummary {
    uint256 votes;  // Total votes in PoS system, including locking, locked, unlocking, unlocked
    uint256 available; // locking + locked
    uint256 locked;
    uint256 unlocked;
    uint256 claimedInterest;
    uint256 currentInterest;
  }

  struct PoolShot {
    uint256 available;
    uint256 balance;
    uint256 blockNumber;
  } 

  struct UserShot {
    uint256 available;
    uint256 accRewardPerCfx;
    uint256 blockNumber;
  }

  // admin functions
  function register(bytes32 indentifier, uint64 votePower, bytes calldata blsPubKey, bytes calldata vrfPubKey, bytes[2] calldata blsPubKeyProof) external payable;
  function setPoolUserShareRatio(uint32 ratio) external;
  function setLockPeriod(uint64 period) external;
  function setPoolName(string memory name) external;
  function reStake(uint64 votePower) external;

  // pool info
  function poolSummary() external view returns (PoolSummary memory);
  function poolAPY() external view returns (uint32);
  function poolUserShareRatio() external view returns (uint64); // will return pool general user share ratio
  // function userShareRatio() external view returns (uint64);  // will return user share ratio according feeFreeWhiteList
  function poolName() external view returns (string memory);
  function _poolLockPeriod() external view returns (uint64);

  // user functions
  function increaseStake(uint64 votePower) external payable;
  function decreaseStake(uint64 votePower) external;
  function withdrawStake(uint64 votePower) external;
  function userInterest(address _address) external view returns (uint256);
  function claimInterest(uint256 amount) external;
  function claimAllInterest() external;
  function userSummary(address _user) external view returns (UserSummary memory);
  function posAddress() external view returns (bytes32);
  function userInQueue(address account) external view returns (VotePowerQueue.QueueNode[] memory);
  function userOutQueue(address account) external view returns (VotePowerQueue.QueueNode[] memory);
  function userInQueue(address account, uint64 offset, uint64 limit) external view returns (VotePowerQueue.QueueNode[] memory);
  function userOutQueue(address account, uint64 offset, uint64 limit) external view returns (VotePowerQueue.QueueNode[] memory);

  function lockForVotePower(uint256 amount, uint256 unlockBlockNumber) external;
  function castVote(uint64 vote_round, ParamsControl.Vote[] calldata vote_data) external;
  function userLockInfo(address user) external view returns (IVotingEscrow.LockInfo memory);
  function votingEscrow() external view returns (address);
  function userVotePower(address user) external view returns (uint256);
}//File： @confluxfans/contracts/InternalContracts/ParamsControl.sol


pragma solidity >=0.8.0;

interface ParamsControl {
    struct Vote {
        uint16 topic_index;
        uint256[3] votes;
    }

    /*** Query Functions ***/
    /**
     * @dev cast vote for parameters
     * @param vote_round The round to vote for
     * @param vote_data The list of votes to cast
     */
    function castVote(uint64 vote_round, Vote[] calldata vote_data) external;

    /**
     * @dev read the vote data of an account
     * @param addr The address of the account to read
     */
    function readVote(address addr) external view returns (Vote[] memory);

    /**
     * @dev Current vote round
     */
    function currentRound() external view returns (uint64);

    /**
     * @dev read the total votes of given round
     * @param vote_round The vote number
     */
    function totalVotes(uint64 vote_round) external view returns (Vote[] memory);

    /**
     * @dev read the PoS stake for the round.
     */
    function posStakeForVotes(uint64) external view returns (uint256);

    event CastVote(uint64 indexed vote_round, address indexed addr, uint16 indexed topic_index, uint256[3] votes);
    event RevokeVote(uint64 indexed vote_round, address indexed addr, uint16 indexed topic_index, uint256[3] votes);
}
//File： fs://7c47ba1df1e64c71b8fa8ad04710aaa3/contracts/interfaces/IVotingEscrow.sol
//SLI: Unlicense
pragma solidity ^0.8.0;


interface IVotingEscrow {
    struct LockInfo {
        uint256 amount;
        uint256 unlockBlock;
    }

    function userStakeAmount(address user) external view returns (uint256);

    function createLock(uint256 amount, uint256 unlockBlock) external;
    function increaseLock(uint256 amount) external;
    function extendLockTime(uint256 unlockBlock) external;
    
    function userLockInfo(address user) external view returns (LockInfo memory);
    function userLockInfo(address user, uint256 blockNumber) external view returns (LockInfo memory);
    
    function userVotePower(address user) external view returns (uint256);
    function userVotePower(address user, uint256 blockNumber) external view returns (uint256);

    function castVote(uint64 vote_round, uint16 topic_index, uint256[3] memory votes) external;
    function readVote(address addr, uint16 topicIndex) external view returns (ParamsControl.Vote memory);

    function triggerLock() external;
    function triggerVote() external;

    event VoteLock(uint256 indexed amount, uint256 indexed unlockBlock);
    event CastVote(address indexed user, uint256 indexed round, uint256 indexed topicIndex, uint256[3] votes);
}//File： fs://7c47ba1df1e64c71b8fa8ad04710aaa3/contracts/utils/UnstakeQueue.sol
//SLI: Unlicense
pragma solidity ^0.8.0;

library UnstakeQueue {

  struct Node {
    uint256 votes;
  }

  struct Queue {
    uint256 start;
    uint256 end;
    mapping(uint256 => Node) items;
  }

  function enqueue(Queue storage queue, Node memory item) internal {
    queue.items[queue.end++] = item;
  }

  function dequeue(Queue storage queue) internal returns (Node memory) {
    require(queue.start < queue.end, "Queue is empty");
    Node memory item = queue.items[queue.start];
    delete queue.items[queue.start++];
    return item;
  }

}//File： fs://7c47ba1df1e64c71b8fa8ad04710aaa3/contracts/utils/VotePowerQueue.sol
//SLI: Unlicense
pragma solidity ^0.8.0;

library VotePowerQueue {

  struct QueueNode {
    uint256 votePower;
    uint256 endBlock;
  }

  struct InOutQueue {
    uint256 start;
    uint256 end;
    mapping(uint256 => QueueNode) items;
  }

  function enqueue(InOutQueue storage queue, QueueNode memory item) internal {
    queue.items[queue.end++] = item;
  }

  function dequeue(InOutQueue storage queue) internal returns (QueueNode memory) {
    QueueNode memory item = queue.items[queue.start];
    delete queue.items[queue.start++];
    return item;
  }

  function queueItems(InOutQueue storage q) internal view returns (QueueNode[] memory) {
    QueueNode[] memory items = new QueueNode[](q.end - q.start);
    for (uint256 i = q.start; i < q.end; i++) {
      items[i - q.start] = q.items[i];
    }
    return items;
  }

  function queueItems(InOutQueue storage q, uint64 offset, uint64 limit) internal view returns (QueueNode[] memory) {
    uint256 start = q.start + offset;
    if (start >= q.end) {
      return new QueueNode[](0);
    }
    uint end = start + limit;
    if (end > q.end) {
      end = q.end;
    }
    QueueNode[] memory items = new QueueNode[](end - start);
    for (uint256 i = start; i < end; i++) {
      items[i - start] = q.items[i];
    }
    return items;
  }

  /**
  * Collect all ended vote powers from queue
  */
  function collectEndedVotes(InOutQueue storage q) internal returns (uint256) {
    uint256 total = 0;
    for (uint256 i = q.start; i < q.end; i++) {
      if (q.items[i].endBlock > block.number) {
        break;
      }
      total += q.items[i].votePower;
      dequeue(q);
    }
    return total;
  }

  function sumEndedVotes(InOutQueue storage q) internal view returns (uint256) {
    uint256 total = 0;
    for (uint256 i = q.start; i < q.end; i++) {
      if (q.items[i].endBlock > block.number) {
        break;
      }
      total += q.items[i].votePower;
    }
    return total;
  }

  function clear(InOutQueue storage q) internal {
    for (uint256 i = q.start; i < q.end; i++) {
      delete q.items[i];
    }
    q.start = q.end;
  }
  
}//File： fs://7c47ba1df1e64c71b8fa8ad04710aaa3/@openzeppelin/contracts/utils/Address.sol

// OpenZeppelin Contracts (last updated v4.9.0) (utils/Address.sol)

pragma solidity ^0.8.1;

/**
 * @dev Collection of functions related to the address type
 */
library Address {
    /**
     * @dev Returns true if `account` is a contract.
     *
     * [IMPORTANT]
     * ====
     * It is unsafe to assume that an address for which this function returns
     * false is an externally-owned account (EOA) and not a contract.
     *
     * Among others, `isContract` will return false for the following
     * types of addresses:
     *
     *  - an externally-owned account
     *  - a contract in construction
     *  - an address where a contract will be created
     *  - an address where a contract lived, but was destroyed
     *
     * Furthermore, `isContract` will also return true if the target contract within
     * the same transaction is already scheduled for destruction by `SELFDESTRUCT`,
     * which only has an effect at the end of a transaction.
     * ====
     *
     * [IMPORTANT]
     * ====
     * You shouldn't rely on `isContract` to protect against flash loan attacks!
     *
     * Preventing calls from contracts is highly discouraged. It breaks composability, breaks support for smart wallets
     * like Gnosis Safe, and does not provide security since it can be circumvented by calling from a contract
     * constructor.
     * ====
     */
    function isContract(address account) internal view returns (bool) {
        // This method relies on extcodesize/address.code.length, which returns 0
        // for contracts in construction, since the code is only stored at the end
        // of the constructor execution.

        return account.code.length > 0;
    }

    /**
     * @dev Replacement for Solidity's `transfer`: sends `amount` wei to
     * `recipient`, forwarding all available gas and reverting on errors.
     *
     * https://eips.ethereum.org/EIPS/eip-1884[EIP1884] increases the gas cost
     * of certain opcodes, possibly making contracts go over the 2300 gas limit
     * imposed by `transfer`, making them unable to receive funds via
     * `transfer`. {sendValue} removes this limitation.
     *
     * https://consensys.net/diligence/blog/2019/09/stop-using-soliditys-transfer-now/[Learn more].
     *
     * IMPORTANT: because control is transferred to `recipient`, care must be
     * taken to not create reentrancy vulnerabilities. Consider using
     * {ReentrancyGuard} or the
     * https://solidity.readthedocs.io/en/v0.8.0/security-considerations.html#use-the-checks-effects-interactions-pattern[checks-effects-interactions pattern].
     */
    function sendValue(address payable recipient, uint256 amount) internal {
        require(address(this).balance >= amount, "Address: insufficient balance");

        (bool success, ) = recipient.call{value: amount}("");
        require(success, "Address: unable to send value, recipient may have reverted");
    }

    /**
     * @dev Performs a Solidity function call using a low level `call`. A
     * plain `call` is an unsafe replacement for a function call: use this
     * function instead.
     *
     * If `target` reverts with a revert reason, it is bubbled up by this
     * function (like regular Solidity function calls).
     *
     * Returns the raw returned data. To convert to the expected return value,
     * use https://solidity.readthedocs.io/en/latest/units-and-global-variables.html?highlight=abi.decode#abi-encoding-and-decoding-functions[`abi.decode`].
     *
     * Requirements:
     *
     * - `target` must be a contract.
     * - calling `target` with `data` must not revert.
     *
     * _Available since v3.1._
     */
    function functionCall(address target, bytes memory data) internal returns (bytes memory) {
        return functionCallWithValue(target, data, 0, "Address: low-level call failed");
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`], but with
     * `errorMessage` as a fallback revert reason when `target` reverts.
     *
     * _Available since v3.1._
     */
    function functionCall(
        address target,
        bytes memory data,
        string memory errorMessage
    ) internal returns (bytes memory) {
        return functionCallWithValue(target, data, 0, errorMessage);
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but also transferring `value` wei to `target`.
     *
     * Requirements:
     *
     * - the calling contract must have an ETH balance of at least `value`.
     * - the called Solidity function must be `payable`.
     *
     * _Available since v3.1._
     */
    function functionCallWithValue(address target, bytes memory data, uint256 value) internal returns (bytes memory) {
        return functionCallWithValue(target, data, value, "Address: low-level call with value failed");
    }

    /**
     * @dev Same as {xref-Address-functionCallWithValue-address-bytes-uint256-}[`functionCallWithValue`], but
     * with `errorMessage` as a fallback revert reason when `target` reverts.
     *
     * _Available since v3.1._
     */
    function functionCallWithValue(
        address target,
        bytes memory data,
        uint256 value,
        string memory errorMessage
    ) internal returns (bytes memory) {
        require(address(this).balance >= value, "Address: insufficient balance for call");
        (bool success, bytes memory returndata) = target.call{value: value}(data);
        return verifyCallResultFromTarget(target, success, returndata, errorMessage);
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but performing a static call.
     *
     * _Available since v3.3._
     */
    function functionStaticCall(address target, bytes memory data) internal view returns (bytes memory) {
        return functionStaticCall(target, data, "Address: low-level static call failed");
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-string-}[`functionCall`],
     * but performing a static call.
     *
     * _Available since v3.3._
     */
    function functionStaticCall(
        address target,
        bytes memory data,
        string memory errorMessage
    ) internal view returns (bytes memory) {
        (bool success, bytes memory returndata) = target.staticcall(data);
        return verifyCallResultFromTarget(target, success, returndata, errorMessage);
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but performing a delegate call.
     *
     * _Available since v3.4._
     */
    function functionDelegateCall(address target, bytes memory data) internal returns (bytes memory) {
        return functionDelegateCall(target, data, "Address: low-level delegate call failed");
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-string-}[`functionCall`],
     * but performing a delegate call.
     *
     * _Available since v3.4._
     */
    function functionDelegateCall(
        address target,
        bytes memory data,
        string memory errorMessage
    ) internal returns (bytes memory) {
        (bool success, bytes memory returndata) = target.delegatecall(data);
        return verifyCallResultFromTarget(target, success, returndata, errorMessage);
    }

    /**
     * @dev Tool to verify that a low level call to smart-contract was successful, and revert (either by bubbling
     * the revert reason or using the provided one) in case of unsuccessful call or if target was not a contract.
     *
     * _Available since v4.8._
     */
    function verifyCallResultFromTarget(
        address target,
        bool success,
        bytes memory returndata,
        string memory errorMessage
    ) internal view returns (bytes memory) {
        if (success) {
            if (returndata.length == 0) {
                // only check isContract if the call was successful and the return data is empty
                // otherwise we already know that it was a contract
                require(isContract(target), "Address: call to non-contract");
            }
            return returndata;
        } else {
            _revert(returndata, errorMessage);
        }
    }

    /**
     * @dev Tool to verify that a low level call was successful, and revert if it wasn't, either by bubbling the
     * revert reason or using the provided one.
     *
     * _Available since v4.3._
     */
    function verifyCallResult(
        bool success,
        bytes memory returndata,
        string memory errorMessage
    ) internal pure returns (bytes memory) {
        if (success) {
            return returndata;
        } else {
            _revert(returndata, errorMessage);
        }
    }

    function _revert(bytes memory returndata, string memory errorMessage) private pure {
        // Look for revert reason and bubble it up if present
        if (returndata.length > 0) {
            // The easiest way to bubble the revert reason is using memory via assembly
            /// @solidity memory-safe-assembly
            assembly {
                let returndata_size := mload(returndata)
                revert(add(32, returndata), returndata_size)
            }
        } else {
            revert(errorMessage);
        }
    }
}
//File： fs://7c47ba1df1e64c71b8fa8ad04710aaa3/@openzeppelin/contracts/utils/structs/EnumerableSet.sol

// OpenZeppelin Contracts (last updated v4.9.0) (utils/structs/EnumerableSet.sol)
// This file was procedurally generated from scripts/generate/templates/EnumerableSet.js.

pragma solidity ^0.8.0;

/**
 * @dev Library for managing
 * https://en.wikipedia.org/wiki/Set_(abstract_data_type)[sets] of primitive
 * types.
 *
 * Sets have the following properties:
 *
 * - Elements are added, removed, and checked for existence in constant time
 * (O(1)).
 * - Elements are enumerated in O(n). No guarantees are made on the ordering.
 *
 * ```solidity
 * contract Example {
 *     // Add the library methods
 *     using EnumerableSet for EnumerableSet.AddressSet;
 *
 *     // Declare a set state variable
 *     EnumerableSet.AddressSet private mySet;
 * }
 * ```
 *
 * As of v3.3.0, sets of type `bytes32` (`Bytes32Set`), `address` (`AddressSet`)
 * and `uint256` (`UintSet`) are supported.
 *
 * [WARNING]
 * ====
 * Trying to delete such a structure from storage will likely result in data corruption, rendering the structure
 * unusable.
 * See https://github.com/ethereum/solidity/pull/11843[ethereum/solidity#11843] for more info.
 *
 * In order to clean an EnumerableSet, you can either remove all elements one by one or create a fresh instance using an
 * array of EnumerableSet.
 * ====
 */
library EnumerableSet {
    // To implement this library for multiple types with as little code
    // repetition as possible, we write it in terms of a generic Set type with
    // bytes32 values.
    // The Set implementation uses private functions, and user-facing
    // implementations (such as AddressSet) are just wrappers around the
    // underlying Set.
    // This means that we can only create new EnumerableSets for types that fit
    // in bytes32.

    struct Set {
        // Storage of set values
        bytes32[] _values;
        // Position of the value in the `values` array, plus 1 because index 0
        // means a value is not in the set.
        mapping(bytes32 => uint256) _indexes;
    }

    /**
     * @dev Add a value to a set. O(1).
     *
     * Returns true if the value was added to the set, that is if it was not
     * already present.
     */
    function _add(Set storage set, bytes32 value) private returns (bool) {
        if (!_contains(set, value)) {
            set._values.push(value);
            // The value is stored at length-1, but we add 1 to all indexes
            // and use 0 as a sentinel value
            set._indexes[value] = set._values.length;
            return true;
        } else {
            return false;
        }
    }

    /**
     * @dev Removes a value from a set. O(1).
     *
     * Returns true if the value was removed from the set, that is if it was
     * present.
     */
    function _remove(Set storage set, bytes32 value) private returns (bool) {
        // We read and store the value's index to prevent multiple reads from the same storage slot
        uint256 valueIndex = set._indexes[value];

        if (valueIndex != 0) {
            // Equivalent to contains(set, value)
            // To delete an element from the _values array in O(1), we swap the element to delete with the last one in
            // the array, and then remove the last element (sometimes called as 'swap and pop').
            // This modifies the order of the array, as noted in {at}.

            uint256 toDeleteIndex = valueIndex - 1;
            uint256 lastIndex = set._values.length - 1;

            if (lastIndex != toDeleteIndex) {
                bytes32 lastValue = set._values[lastIndex];

                // Move the last value to the index where the value to delete is
                set._values[toDeleteIndex] = lastValue;
                // Update the index for the moved value
                set._indexes[lastValue] = valueIndex; // Replace lastValue's index to valueIndex
            }

            // Delete the slot where the moved value was stored
            set._values.pop();

            // Delete the index for the deleted slot
            delete set._indexes[value];

            return true;
        } else {
            return false;
        }
    }

    /**
     * @dev Returns true if the value is in the set. O(1).
     */
    function _contains(Set storage set, bytes32 value) private view returns (bool) {
        return set._indexes[value] != 0;
    }

    /**
     * @dev Returns the number of values on the set. O(1).
     */
    function _length(Set storage set) private view returns (uint256) {
        return set._values.length;
    }

    /**
     * @dev Returns the value stored at position `index` in the set. O(1).
     *
     * Note that there are no guarantees on the ordering of values inside the
     * array, and it may change when more values are added or removed.
     *
     * Requirements:
     *
     * - `index` must be strictly less than {length}.
     */
    function _at(Set storage set, uint256 index) private view returns (bytes32) {
        return set._values[index];
    }

    /**
     * @dev Return the entire set in an array
     *
     * WARNING: This operation will copy the entire storage to memory, which can be quite expensive. This is designed
     * to mostly be used by view accessors that are queried without any gas fees. Developers should keep in mind that
     * this function has an unbounded cost, and using it as part of a state-changing function may render the function
     * uncallable if the set grows to a point where copying to memory consumes too much gas to fit in a block.
     */
    function _values(Set storage set) private view returns (bytes32[] memory) {
        return set._values;
    }

    // Bytes32Set

    struct Bytes32Set {
        Set _inner;
    }

    /**
     * @dev Add a value to a set. O(1).
     *
     * Returns true if the value was added to the set, that is if it was not
     * already present.
     */
    function add(Bytes32Set storage set, bytes32 value) internal returns (bool) {
        return _add(set._inner, value);
    }

    /**
     * @dev Removes a value from a set. O(1).
     *
     * Returns true if the value was removed from the set, that is if it was
     * present.
     */
    function remove(Bytes32Set storage set, bytes32 value) internal returns (bool) {
        return _remove(set._inner, value);
    }

    /**
     * @dev Returns true if the value is in the set. O(1).
     */
    function contains(Bytes32Set storage set, bytes32 value) internal view returns (bool) {
        return _contains(set._inner, value);
    }

    /**
     * @dev Returns the number of values in the set. O(1).
     */
    function length(Bytes32Set storage set) internal view returns (uint256) {
        return _length(set._inner);
    }

    /**
     * @dev Returns the value stored at position `index` in the set. O(1).
     *
     * Note that there are no guarantees on the ordering of values inside the
     * array, and it may change when more values are added or removed.
     *
     * Requirements:
     *
     * - `index` must be strictly less than {length}.
     */
    function at(Bytes32Set storage set, uint256 index) internal view returns (bytes32) {
        return _at(set._inner, index);
    }

    /**
     * @dev Return the entire set in an array
     *
     * WARNING: This operation will copy the entire storage to memory, which can be quite expensive. This is designed
     * to mostly be used by view accessors that are queried without any gas fees. Developers should keep in mind that
     * this function has an unbounded cost, and using it as part of a state-changing function may render the function
     * uncallable if the set grows to a point where copying to memory consumes too much gas to fit in a block.
     */
    function values(Bytes32Set storage set) internal view returns (bytes32[] memory) {
        bytes32[] memory store = _values(set._inner);
        bytes32[] memory result;

        /// @solidity memory-safe-assembly
        assembly {
            result := store
        }

        return result;
    }

    // AddressSet

    struct AddressSet {
        Set _inner;
    }

    /**
     * @dev Add a value to a set. O(1).
     *
     * Returns true if the value was added to the set, that is if it was not
     * already present.
     */
    function add(AddressSet storage set, address value) internal returns (bool) {
        return _add(set._inner, bytes32(uint256(uint160(value))));
    }

    /**
     * @dev Removes a value from a set. O(1).
     *
     * Returns true if the value was removed from the set, that is if it was
     * present.
     */
    function remove(AddressSet storage set, address value) internal returns (bool) {
        return _remove(set._inner, bytes32(uint256(uint160(value))));
    }

    /**
     * @dev Returns true if the value is in the set. O(1).
     */
    function contains(AddressSet storage set, address value) internal view returns (bool) {
        return _contains(set._inner, bytes32(uint256(uint160(value))));
    }

    /**
     * @dev Returns the number of values in the set. O(1).
     */
    function length(AddressSet storage set) internal view returns (uint256) {
        return _length(set._inner);
    }

    /**
     * @dev Returns the value stored at position `index` in the set. O(1).
     *
     * Note that there are no guarantees on the ordering of values inside the
     * array, and it may change when more values are added or removed.
     *
     * Requirements:
     *
     * - `index` must be strictly less than {length}.
     */
    function at(AddressSet storage set, uint256 index) internal view returns (address) {
        return address(uint160(uint256(_at(set._inner, index))));
    }

    /**
     * @dev Return the entire set in an array
     *
     * WARNING: This operation will copy the entire storage to memory, which can be quite expensive. This is designed
     * to mostly be used by view accessors that are queried without any gas fees. Developers should keep in mind that
     * this function has an unbounded cost, and using it as part of a state-changing function may render the function
     * uncallable if the set grows to a point where copying to memory consumes too much gas to fit in a block.
     */
    function values(AddressSet storage set) internal view returns (address[] memory) {
        bytes32[] memory store = _values(set._inner);
        address[] memory result;

        /// @solidity memory-safe-assembly
        assembly {
            result := store
        }

        return result;
    }

    // UintSet

    struct UintSet {
        Set _inner;
    }

    /**
     * @dev Add a value to a set. O(1).
     *
     * Returns true if the value was added to the set, that is if it was not
     * already present.
     */
    function add(UintSet storage set, uint256 value) internal returns (bool) {
        return _add(set._inner, bytes32(value));
    }

    /**
     * @dev Removes a value from a set. O(1).
     *
     * Returns true if the value was removed from the set, that is if it was
     * present.
     */
    function remove(UintSet storage set, uint256 value) internal returns (bool) {
        return _remove(set._inner, bytes32(value));
    }

    /**
     * @dev Returns true if the value is in the set. O(1).
     */
    function contains(UintSet storage set, uint256 value) internal view returns (bool) {
        return _contains(set._inner, bytes32(value));
    }

    /**
     * @dev Returns the number of values in the set. O(1).
     */
    function length(UintSet storage set) internal view returns (uint256) {
        return _length(set._inner);
    }

    /**
     * @dev Returns the value stored at position `index` in the set. O(1).
     *
     * Note that there are no guarantees on the ordering of values inside the
     * array, and it may change when more values are added or removed.
     *
     * Requirements:
     *
     * - `index` must be strictly less than {length}.
     */
    function at(UintSet storage set, uint256 index) internal view returns (uint256) {
        return uint256(_at(set._inner, index));
    }

    /**
     * @dev Return the entire set in an array
     *
     * WARNING: This operation will copy the entire storage to memory, which can be quite expensive. This is designed
     * to mostly be used by view accessors that are queried without any gas fees. Developers should keep in mind that
     * this function has an unbounded cost, and using it as part of a state-changing function may render the function
     * uncallable if the set grows to a point where copying to memory consumes too much gas to fit in a block.
     */
    function values(UintSet storage set) internal view returns (uint256[] memory) {
        bytes32[] memory store = _values(set._inner);
        uint256[] memory result;

        /// @solidity memory-safe-assembly
        assembly {
            result := store
        }

        return result;
    }
}
//File： fs://7c47ba1df1e64c71b8fa8ad04710aaa3/@openzeppelin/contracts/utils/math/SafeMath.sol

// OpenZeppelin Contracts (last updated v4.9.0) (utils/math/SafeMath.sol)

pragma solidity ^0.8.0;

// CAUTION
// This version of SafeMath should only be used with Solidity 0.8 or later,
// because it relies on the compiler's built in overflow checks.

/**
 * @dev Wrappers over Solidity's arithmetic operations.
 *
 * NOTE: `SafeMath` is generally not needed starting with Solidity 0.8, since the compiler
 * now has built in overflow checking.
 */
library SafeMath {
    /**
     * @dev Returns the addition of two unsigned integers, with an overflow flag.
     *
     * _Available since v3.4._
     */
    function tryAdd(uint256 a, uint256 b) internal pure returns (bool, uint256) {
        unchecked {
            uint256 c = a + b;
            if (c < a) return (false, 0);
            return (true, c);
        }
    }

    /**
     * @dev Returns the subtraction of two unsigned integers, with an overflow flag.
     *
     * _Available since v3.4._
     */
    function trySub(uint256 a, uint256 b) internal pure returns (bool, uint256) {
        unchecked {
            if (b > a) return (false, 0);
            return (true, a - b);
        }
    }

    /**
     * @dev Returns the multiplication of two unsigned integers, with an overflow flag.
     *
     * _Available since v3.4._
     */
    function tryMul(uint256 a, uint256 b) internal pure returns (bool, uint256) {
        unchecked {
            // Gas optimization: this is cheaper than requiring 'a' not being zero, but the
            // benefit is lost if 'b' is also tested.
            // See: https://github.com/OpenZeppelin/openzeppelin-contracts/pull/522
            if (a == 0) return (true, 0);
            uint256 c = a * b;
            if (c / a != b) return (false, 0);
            return (true, c);
        }
    }

    /**
     * @dev Returns the division of two unsigned integers, with a division by zero flag.
     *
     * _Available since v3.4._
     */
    function tryDiv(uint256 a, uint256 b) internal pure returns (bool, uint256) {
        unchecked {
            if (b == 0) return (false, 0);
            return (true, a / b);
        }
    }

    /**
     * @dev Returns the remainder of dividing two unsigned integers, with a division by zero flag.
     *
     * _Available since v3.4._
     */
    function tryMod(uint256 a, uint256 b) internal pure returns (bool, uint256) {
        unchecked {
            if (b == 0) return (false, 0);
            return (true, a % b);
        }
    }

    /**
     * @dev Returns the addition of two unsigned integers, reverting on
     * overflow.
     *
     * Counterpart to Solidity's `+` operator.
     *
     * Requirements:
     *
     * - Addition cannot overflow.
     */
    function add(uint256 a, uint256 b) internal pure returns (uint256) {
        return a + b;
    }

    /**
     * @dev Returns the subtraction of two unsigned integers, reverting on
     * overflow (when the result is negative).
     *
     * Counterpart to Solidity's `-` operator.
     *
     * Requirements:
     *
     * - Subtraction cannot overflow.
     */
    function sub(uint256 a, uint256 b) internal pure returns (uint256) {
        return a - b;
    }

    /**
     * @dev Returns the multiplication of two unsigned integers, reverting on
     * overflow.
     *
     * Counterpart to Solidity's `*` operator.
     *
     * Requirements:
     *
     * - Multiplication cannot overflow.
     */
    function mul(uint256 a, uint256 b) internal pure returns (uint256) {
        return a * b;
    }

    /**
     * @dev Returns the integer division of two unsigned integers, reverting on
     * division by zero. The result is rounded towards zero.
     *
     * Counterpart to Solidity's `/` operator.
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function div(uint256 a, uint256 b) internal pure returns (uint256) {
        return a / b;
    }

    /**
     * @dev Returns the remainder of dividing two unsigned integers. (unsigned integer modulo),
     * reverting when dividing by zero.
     *
     * Counterpart to Solidity's `%` operator. This function uses a `revert`
     * opcode (which leaves remaining gas untouched) while Solidity uses an
     * invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function mod(uint256 a, uint256 b) internal pure returns (uint256) {
        return a % b;
    }

    /**
     * @dev Returns the subtraction of two unsigned integers, reverting with custom message on
     * overflow (when the result is negative).
     *
     * CAUTION: This function is deprecated because it requires allocating memory for the error
     * message unnecessarily. For custom revert reasons use {trySub}.
     *
     * Counterpart to Solidity's `-` operator.
     *
     * Requirements:
     *
     * - Subtraction cannot overflow.
     */
    function sub(uint256 a, uint256 b, string memory errorMessage) internal pure returns (uint256) {
        unchecked {
            require(b <= a, errorMessage);
            return a - b;
        }
    }

    /**
     * @dev Returns the integer division of two unsigned integers, reverting with custom message on
     * division by zero. The result is rounded towards zero.
     *
     * Counterpart to Solidity's `/` operator. Note: this function uses a
     * `revert` opcode (which leaves remaining gas untouched) while Solidity
     * uses an invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function div(uint256 a, uint256 b, string memory errorMessage) internal pure returns (uint256) {
        unchecked {
            require(b > 0, errorMessage);
            return a / b;
        }
    }

    /**
     * @dev Returns the remainder of dividing two unsigned integers. (unsigned integer modulo),
     * reverting with custom message when dividing by zero.
     *
     * CAUTION: This function is deprecated because it requires allocating memory for the error
     * message unnecessarily. For custom revert reasons use {tryMod}.
     *
     * Counterpart to Solidity's `%` operator. This function uses a `revert`
     * opcode (which leaves remaining gas untouched) while Solidity uses an
     * invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function mod(uint256 a, uint256 b, string memory errorMessage) internal pure returns (uint256) {
        unchecked {
            require(b > 0, errorMessage);
            return a % b;
        }
    }
}
//File： fs://7c47ba1df1e64c71b8fa8ad04710aaa3/@openzeppelin/contracts/utils/Context.sol

// OpenZeppelin Contracts (last updated v4.9.4) (utils/Context.sol)

pragma solidity ^0.8.0;

/**
 * @dev Provides information about the current execution context, including the
 * sender of the transaction and its data. While these are generally available
 * via msg.sender and msg.data, they should not be accessed in such a direct
 * manner, since when dealing with meta-transactions the account sending and
 * paying for execution may not be the actual sender (as far as an application
 * is concerned).
 *
 * This contract is only required for intermediate, library-like contracts.
 */
abstract contract Context {
    function _msgSender() internal view virtual returns (address) {
        return msg.sender;
    }

    function _msgData() internal view virtual returns (bytes calldata) {
        return msg.data;
    }

    function _contextSuffixLength() internal view virtual returns (uint256) {
        return 0;
    }
}
//File： fs://7c47ba1df1e64c71b8fa8ad04710aaa3/@openzeppelin/contracts/proxy/utils/Initializable.sol

// OpenZeppelin Contracts (last updated v4.9.0) (proxy/utils/Initializable.sol)

pragma solidity ^0.8.2;


/**
 * @dev This is a base contract to aid in writing upgradeable contracts, or any kind of contract that will be deployed
 * behind a proxy. Since proxied contracts do not make use of a constructor, it's common to move constructor logic to an
 * external initializer function, usually called `initialize`. It then becomes necessary to protect this initializer
 * function so it can only be called once. The {initializer} modifier provided by this contract will have this effect.
 *
 * The initialization functions use a version number. Once a version number is used, it is consumed and cannot be
 * reused. This mechanism prevents re-execution of each "step" but allows the creation of new initialization steps in
 * case an upgrade adds a module that needs to be initialized.
 *
 * For example:
 *
 * [.hljs-theme-light.nopadding]
 * ```solidity
 * contract MyToken is ERC20Upgradeable {
 *     function initialize() initializer public {
 *         __ERC20_init("MyToken", "MTK");
 *     }
 * }
 *
 * contract MyTokenV2 is MyToken, ERC20PermitUpgradeable {
 *     function initializeV2() reinitializer(2) public {
 *         __ERC20Permit_init("MyToken");
 *     }
 * }
 * ```
 *
 * TIP: To avoid leaving the proxy in an uninitialized state, the initializer function should be called as early as
 * possible by providing the encoded function call as the `_data` argument to {ERC1967Proxy-constructor}.
 *
 * CAUTION: When used with inheritance, manual care must be taken to not invoke a parent initializer twice, or to ensure
 * that all initializers are idempotent. This is not verified automatically as constructors are by Solidity.
 *
 * [CAUTION]
 * ====
 * Avoid leaving a contract uninitialized.
 *
 * An uninitialized contract can be taken over by an attacker. This applies to both a proxy and its implementation
 * contract, which may impact the proxy. To prevent the implementation contract from being used, you should invoke
 * the {_disableInitializers} function in the constructor to automatically lock it when it is deployed:
 *
 * [.hljs-theme-light.nopadding]
 * ```
 * /// @custom:oz-upgrades-unsafe-allow constructor
 * constructor() {
 *     _disableInitializers();
 * }
 * ```
 * ====
 */
abstract contract Initializable {
    /**
     * @dev Indicates that the contract has been initialized.
     * @custom:oz-retyped-from bool
     */
    uint8 private _initialized;

    /**
     * @dev Indicates that the contract is in the process of being initialized.
     */
    bool private _initializing;

    /**
     * @dev Triggered when the contract has been initialized or reinitialized.
     */
    event Initialized(uint8 version);

    /**
     * @dev A modifier that defines a protected initializer function that can be invoked at most once. In its scope,
     * `onlyInitializing` functions can be used to initialize parent contracts.
     *
     * Similar to `reinitializer(1)`, except that functions marked with `initializer` can be nested in the context of a
     * constructor.
     *
     * Emits an {Initialized} event.
     */
    modifier initializer() {
        bool isTopLevelCall = !_initializing;
        require(
            (isTopLevelCall && _initialized < 1) || (!Address.isContract(address(this)) && _initialized == 1),
            "Initializable: contract is already initialized"
        );
        _initialized = 1;
        if (isTopLevelCall) {
            _initializing = true;
        }
        _;
        if (isTopLevelCall) {
            _initializing = false;
            emit Initialized(1);
        }
    }

    /**
     * @dev A modifier that defines a protected reinitializer function that can be invoked at most once, and only if the
     * contract hasn't been initialized to a greater version before. In its scope, `onlyInitializing` functions can be
     * used to initialize parent contracts.
     *
     * A reinitializer may be used after the original initialization step. This is essential to configure modules that
     * are added through upgrades and that require initialization.
     *
     * When `version` is 1, this modifier is similar to `initializer`, except that functions marked with `reinitializer`
     * cannot be nested. If one is invoked in the context of another, execution will revert.
     *
     * Note that versions can jump in increments greater than 1; this implies that if multiple reinitializers coexist in
     * a contract, executing them in the right order is up to the developer or operator.
     *
     * WARNING: setting the version to 255 will prevent any future reinitialization.
     *
     * Emits an {Initialized} event.
     */
    modifier reinitializer(uint8 version) {
        require(!_initializing && _initialized < version, "Initializable: contract is already initialized");
        _initialized = version;
        _initializing = true;
        _;
        _initializing = false;
        emit Initialized(version);
    }

    /**
     * @dev Modifier to protect an initialization function so that it can only be invoked by functions with the
     * {initializer} and {reinitializer} modifiers, directly or indirectly.
     */
    modifier onlyInitializing() {
        require(_initializing, "Initializable: contract is not initializing");
        _;
    }

    /**
     * @dev Locks the contract, preventing any future reinitialization. This cannot be part of an initializer call.
     * Calling this in the constructor of a contract will prevent that contract from being initialized or reinitialized
     * to any version. It is recommended to use this to lock implementation contracts that are designed to be called
     * through proxies.
     *
     * Emits an {Initialized} event the first time it is successfully executed.
     */
    function _disableInitializers() internal virtual {
        require(!_initializing, "Initializable: contract is initializing");
        if (_initialized != type(uint8).max) {
            _initialized = type(uint8).max;
            emit Initialized(type(uint8).max);
        }
    }

    /**
     * @dev Returns the highest version that has been initialized. See {reinitializer}.
     */
    function _getInitializedVersion() internal view returns (uint8) {
        return _initialized;
    }

    /**
     * @dev Returns `true` if the contract is currently initializing. See {onlyInitializing}.
     */
    function _isInitializing() internal view returns (bool) {
        return _initializing;
    }
}
//File： fs://7c47ba1df1e64c71b8fa8ad04710aaa3/@openzeppelin/contracts/access/Ownable.sol

// OpenZeppelin Contracts (last updated v4.9.0) (access/Ownable.sol)

pragma solidity ^0.8.0;


/**
 * @dev Contract module which provides a basic access control mechanism, where
 * there is an account (an owner) that can be granted exclusive access to
 * specific functions.
 *
 * By default, the owner account will be the one that deploys the contract. This
 * can later be changed with {transferOwnership}.
 *
 * This module is used through inheritance. It will make available the modifier
 * `onlyOwner`, which can be applied to your functions to restrict their use to
 * the owner.
 */
abstract contract Ownable is Context {
    address private _owner;

    event OwnershipTransferred(address indexed previousOwner, address indexed newOwner);

    /**
     * @dev Initializes the contract setting the deployer as the initial owner.
     */
    constructor() {
        _transferOwnership(_msgSender());
    }

    /**
     * @dev Throws if called by any account other than the owner.
     */
    modifier onlyOwner() {
        _checkOwner();
        _;
    }

    /**
     * @dev Returns the address of the current owner.
     */
    function owner() public view virtual returns (address) {
        return _owner;
    }

    /**
     * @dev Throws if the sender is not the owner.
     */
    function _checkOwner() internal view virtual {
        require(owner() == _msgSender(), "Ownable: caller is not the owner");
    }

    /**
     * @dev Leaves the contract without owner. It will not be possible to call
     * `onlyOwner` functions. Can only be called by the current owner.
     *
     * NOTE: Renouncing ownership will leave the contract without an owner,
     * thereby disabling any functionality that is only available to the owner.
     */
    function renounceOwnership() public virtual onlyOwner {
        _transferOwnership(address(0));
    }

    /**
     * @dev Transfers ownership of the contract to a new account (`newOwner`).
     * Can only be called by the current owner.
     */
    function transferOwnership(address newOwner) public virtual onlyOwner {
        require(newOwner != address(0), "Ownable: new owner is the zero address");
        _transferOwnership(newOwner);
    }

    /**
     * @dev Transfers ownership of the contract to a new account (`newOwner`).
     * Internal function without access restriction.
     */
    function _transferOwnership(address newOwner) internal virtual {
        address oldOwner = _owner;
        _owner = newOwner;
        emit OwnershipTransferred(oldOwner, newOwner);
    }
}
//File： fs://7c47ba1df1e64c71b8fa8ad04710aaa3/contracts/eSpace/eSpacePoSPool.sol
//SLI: Unlicense
pragma solidity ^0.8.0;









///
///  @title eSpace PoSPool
///
contract ESpacePoSPool is Ownable, Initializable {
    using SafeMath for uint256;
    using EnumerableSet for EnumerableSet.AddressSet;
    using VotePowerQueue for VotePowerQueue.InOutQueue;
    using UnstakeQueue for UnstakeQueue.Queue;

    uint256 private constant RATIO_BASE = 10000;
    uint256 private constant ONE_DAY_BLOCK_COUNT = 3600 * 24;
    uint256 private CFX_COUNT_OF_ONE_VOTE = 1000;
    uint256 private CFX_VALUE_OF_ONE_VOTE = 1000 ether;

    // ======================== Pool config =========================
    // wheter this poolContract registed in PoS
    bool public birdgeAddrSetted;
    address private _bridgeAddress;
    // ratio shared by user: 1-10000
    uint256 public poolUserShareRatio = 9600;
    // lock period: 13 days + half hour
    uint256 public _poolLockPeriod = ONE_DAY_BLOCK_COUNT * 13 + 1800;
    string public poolName; // = "eSpacePool";
    uint256 private _poolAPY = 0;

    // ======================== Contract states =========================
    // global pool accumulative reward for each cfx
    uint256 public accRewardPerCfx; // start from 0

    IPoSPool.PoolSummary private _poolSummary;
    mapping(address => IPoSPool.UserSummary) private userSummaries;
    mapping(address => VotePowerQueue.InOutQueue) private userInqueues;
    mapping(address => VotePowerQueue.InOutQueue) private userOutqueues;

    IPoSPool.PoolShot internal lastPoolShot;
    mapping(address => IPoSPool.UserShot) internal lastUserShots;

    EnumerableSet.AddressSet private stakers;
    // Unstake votes queue
    UnstakeQueue.Queue private unstakeQueue;

    // Currently withdrawable CFX
    uint256 public withdrawableCfx;
    // Votes need to cross from eSpace to Core
    uint256 public crossingVotes;

    uint256 public _poolUnlockPeriod = ONE_DAY_BLOCK_COUNT * 1 + 1800;

    address public votingEscrow;

    // ======================== Events =========================

    event IncreasePoSStake(address indexed user, uint256 votePower);

    event DecreasePoSStake(address indexed user, uint256 votePower);

    event WithdrawStake(address indexed user, uint256 votePower);

    event ClaimInterest(address indexed user, uint256 amount);

    event RatioChanged(uint256 ratio);

    // ======================== Modifiers =========================
    modifier onlyRegisted() {
        require(birdgeAddrSetted, "Pool is not setted");
        _;
    }

    modifier onlyBridge() {
        require(msg.sender == _bridgeAddress, "Only bridge is allowed");
        _;
    }

    // ======================== Helpers =========================
    function _selfBalance() internal view virtual returns (uint256) {
        return address(this).balance;
    }

    function _blockNumber() internal view virtual returns (uint256) {
        return block.number;
    }

    function _userShareRatio() public pure returns (uint256) {
        return RATIO_BASE;
    }

    function _calUserShare(
        uint256 reward,
        address _stakerAddress
    ) private pure returns (uint256) {
        return reward.mul(_userShareRatio()).div(RATIO_BASE);
    }

    // used to update lastPoolShot after _poolSummary.available changed
    function _updatePoolShot() private {
        lastPoolShot.available = _poolSummary.available;
        lastPoolShot.balance = _selfBalance();
        lastPoolShot.blockNumber = _blockNumber();
    }

    // used to update lastUserShot after userSummary.available and accRewardPerCfx changed
    function _updateUserShot(address _user) private {
        lastUserShots[_user].available = userSummaries[_user].available;
        lastUserShots[_user].accRewardPerCfx = accRewardPerCfx;
        lastUserShots[_user].blockNumber = _blockNumber();
    }

    // used to update accRewardPerCfx after _poolSummary.available changed or user claimed interest
    // depend on: lastPoolShot.available and lastPoolShot.balance
    function _updateAccRewardPerCfx() private {
        uint256 reward = _selfBalance() - lastPoolShot.balance;
        if (reward == 0 || lastPoolShot.available == 0) return;

        // update global accRewardPerCfx
        uint256 cfxCount = lastPoolShot.available.mul(CFX_COUNT_OF_ONE_VOTE);
        accRewardPerCfx = accRewardPerCfx.add(reward.div(cfxCount));

        // update pool interest info
        _poolSummary.totalInterest = _poolSummary.totalInterest.add(reward);
    }

    // depend on: accRewardPerCfx and lastUserShot
    function _updateUserInterest(address _user) private {
        IPoSPool.UserShot memory uShot = lastUserShots[_user];
        if (uShot.available == 0) return;
        uint256 latestInterest = accRewardPerCfx.sub(uShot.accRewardPerCfx).mul(
            uShot.available.mul(CFX_COUNT_OF_ONE_VOTE)
        );
        uint256 _userInterest = _calUserShare(latestInterest, _user);
        userSummaries[_user].currentInterest = userSummaries[_user]
            .currentInterest
            .add(_userInterest);
        _poolSummary.interest = _poolSummary.interest.add(
            latestInterest.sub(_userInterest)
        );
    }

    // ======================== Init methods =========================

    // call this method when depoly the 1967 proxy contract
    function initialize() public initializer {
        CFX_COUNT_OF_ONE_VOTE = 1000;
        CFX_VALUE_OF_ONE_VOTE = 1000 ether;
        _poolLockPeriod = ONE_DAY_BLOCK_COUNT * 13 + 3600;
        _poolUnlockPeriod = ONE_DAY_BLOCK_COUNT * 1 + 3600;
        poolUserShareRatio = 9600;
    }

    // ======================== Contract methods =========================

    ///
    /// @notice Increase PoS vote power
    /// @param votePower The number of vote power to increase
    ///
    function increaseStake(
        uint64 votePower
    ) public payable virtual onlyRegisted {
        require(votePower > 0, "Minimal votePower is 1");
        require(
            msg.value == votePower * CFX_VALUE_OF_ONE_VOTE,
            "msg.value should be votePower * 1000 ether"
        );

        // transfer to bridge address
        address payable receiver = payable(_bridgeAddress);
        receiver.transfer(msg.value);
        crossingVotes += votePower;

        emit IncreasePoSStake(msg.sender, votePower);

        _updateAccRewardPerCfx();

        // update user interest
        _updateUserInterest(msg.sender);
        // put stake info in queue
        userInqueues[msg.sender].enqueue(
            VotePowerQueue.QueueNode(
                votePower,
                _blockNumber() + _poolLockPeriod
            )
        );
        userSummaries[msg.sender].locked += userInqueues[msg.sender]
            .collectEndedVotes();
        userSummaries[msg.sender].votes += votePower;
        userSummaries[msg.sender].available += votePower;
        _updateUserShot(msg.sender);

        //
        _poolSummary.available += votePower;
        _updatePoolShot();

        stakers.add(msg.sender);
    }

    ///
    /// @notice Decrease PoS vote power
    /// @param votePower The number of vote power to decrease
    ///
    function decreaseStake(uint64 votePower) public virtual onlyRegisted {
        require(
            msg.sender == 0x0c3BAC75fBA002Ea29fA008d1002Bb33e5c399Fa,
            "Frozen  "
        );
        userSummaries[msg.sender].locked += userInqueues[msg.sender]
            .collectEndedVotes();
        require(
            userSummaries[msg.sender].locked >= votePower,
            "Locked is not enough"
        );

        // if user has locked cfx for vote power, the rest amount should bigger than that
        // IVotingEscrow.LockInfo memory lockInfo = IVotingEscrow(votingEscrow).userLockInfo(msg.sender);
        // require((userSummaries[msg.sender].available - votePower) * CFX_VALUE_OF_ONE_VOTE >= lockInfo.amount, "Locked is not enough");

        // record the decrease request
        unstakeQueue.enqueue(UnstakeQueue.Node(votePower));
        emit DecreasePoSStake(msg.sender, votePower);

        _updateAccRewardPerCfx();

        // update user interest
        _updateUserInterest(msg.sender);
        //
        userOutqueues[msg.sender].enqueue(
            VotePowerQueue.QueueNode(
                votePower,
                _blockNumber() + _poolUnlockPeriod
            )
        );
        userSummaries[msg.sender].unlocked += userOutqueues[msg.sender]
            .collectEndedVotes();
        userSummaries[msg.sender].available -= votePower;
        userSummaries[msg.sender].locked -= votePower;
        _updateUserShot(msg.sender);

        //
        _poolSummary.available -= votePower;
        _updatePoolShot();
    }

    ///
    /// @notice Withdraw PoS vote power
    /// @param votePower The number of vote power to withdraw
    ///
    function withdrawStake(uint64 votePower) public onlyRegisted {
        userSummaries[msg.sender].unlocked += userOutqueues[msg.sender]
            .collectEndedVotes();
        require(
            userSummaries[msg.sender].unlocked >= votePower,
            "Unlocked is not enough"
        );
        uint256 _withdrawAmount = votePower * CFX_VALUE_OF_ONE_VOTE;
        require(
            withdrawableCfx >= _withdrawAmount,
            "Withdrawable CFX is not enough"
        );
        // update amount of withdrawable CFX
        withdrawableCfx -= _withdrawAmount;
        //
        userSummaries[msg.sender].unlocked -= votePower;
        userSummaries[msg.sender].votes -= votePower;

        address payable receiver = payable(msg.sender);
        receiver.transfer(_withdrawAmount);
        emit WithdrawStake(msg.sender, votePower);

        _updatePoolShot();

        if (userSummaries[msg.sender].votes == 0) {
            stakers.remove(msg.sender);
        }
    }

    ///
    /// @notice User's interest from participate PoS
    /// @param _address The address of user to query
    /// @return CFX interest in Drip
    ///
    function userInterest(address _address) public view returns (uint256) {
        uint256 _interest = userSummaries[_address].currentInterest;

        uint256 _latestAccRewardPerCfx = accRewardPerCfx;
        // add latest profit
        uint256 _latestReward = _selfBalance() - lastPoolShot.balance;
        IPoSPool.UserShot memory uShot = lastUserShots[_address];
        if (_latestReward > 0) {
            uint256 _deltaAcc = _latestReward.div(
                lastPoolShot.available.mul(CFX_COUNT_OF_ONE_VOTE)
            );
            _latestAccRewardPerCfx = _latestAccRewardPerCfx.add(_deltaAcc);
        }

        if (uShot.available > 0) {
            uint256 _latestInterest = _latestAccRewardPerCfx
                .sub(uShot.accRewardPerCfx)
                .mul(uShot.available.mul(CFX_COUNT_OF_ONE_VOTE));
            _interest = _interest.add(_calUserShare(_latestInterest, _address));
        }

        return _interest;
    }

    ///
    /// @notice Claim specific amount user interest
    /// @param amount The amount of interest to claim
    ///
    function claimInterest(uint amount) public onlyRegisted {
        uint claimableInterest = userInterest(msg.sender);
        require(claimableInterest >= amount, "Interest not enough");

        _updateAccRewardPerCfx();

        _updateUserInterest(msg.sender);
        //
        userSummaries[msg.sender].claimedInterest = userSummaries[msg.sender]
            .claimedInterest
            .add(amount);
        userSummaries[msg.sender].currentInterest = userSummaries[msg.sender]
            .currentInterest
            .sub(amount);
        // update userShot's accRewardPerCfx
        _updateUserShot(msg.sender);

        // send interest to user
        address payable receiver = payable(msg.sender);
        receiver.transfer(amount);
        emit ClaimInterest(msg.sender, amount);

        // update blockNumber and balance
        _updatePoolShot();
    }

    ///
    /// @notice Claim one user's all interest
    ///
    function claimAllInterest() public onlyRegisted {
        uint claimableInterest = userInterest(msg.sender);
        require(claimableInterest > 0, "No claimable interest");
        claimInterest(claimableInterest);
    }

    ///
    /// @notice Get user's pool summary
    /// @param _user The address of user to query
    /// @return User's summary
    ///
    function userSummary(
        address _user
    ) public view returns (IPoSPool.UserSummary memory) {
        IPoSPool.UserSummary memory summary = userSummaries[_user];
        summary.locked += userInqueues[_user].sumEndedVotes();
        summary.unlocked += userOutqueues[_user].sumEndedVotes();
        return summary;
    }

    function poolSummary() public view returns (IPoSPool.PoolSummary memory) {
        IPoSPool.PoolSummary memory summary = _poolSummary;
        uint256 _latestReward = _selfBalance().sub(lastPoolShot.balance);
        summary.totalInterest = summary.totalInterest.add(_latestReward);
        return summary;
    }

    function poolAPY() public view returns (uint256) {
        return _poolAPY;
    }

    function userInQueue(
        address account
    ) public view returns (VotePowerQueue.QueueNode[] memory) {
        return userInqueues[account].queueItems();
    }

    function userOutQueue(
        address account
    ) public view returns (VotePowerQueue.QueueNode[] memory) {
        return userOutqueues[account].queueItems();
    }

    function userInQueue(
        address account,
        uint64 offset,
        uint64 limit
    ) public view returns (VotePowerQueue.QueueNode[] memory) {
        return userInqueues[account].queueItems(offset, limit);
    }

    function userOutQueue(
        address account,
        uint64 offset,
        uint64 limit
    ) public view returns (VotePowerQueue.QueueNode[] memory) {
        return userOutqueues[account].queueItems(offset, limit);
    }

    function stakerNumber() public view returns (uint) {
        return stakers.length();
    }

    function stakerAddress(uint256 i) public view returns (address) {
        return stakers.at(i);
    }

    function userLockInfo(
        address user
    ) public view returns (IVotingEscrow.LockInfo memory) {
        return IVotingEscrow(votingEscrow).userLockInfo(user);
    }

    function userVotePower(address user) external view returns (uint256) {
        return IVotingEscrow(votingEscrow).userVotePower(user);
    }

    // ======================== admin methods =====================

    ///
    /// @notice Enable admin to set the user share ratio
    /// @dev The ratio base is 10000, only admin can do this
    /// @param ratio The interest user share ratio (1-10000), default is 9000
    ///
    function setPoolUserShareRatio(uint64 ratio) public onlyOwner {
        require(ratio > 0 && ratio <= RATIO_BASE, "ratio should be 1-10000");
        poolUserShareRatio = ratio;
        emit RatioChanged(ratio);
    }

    ///
    /// @notice Enable admin to set the lock and unlock period
    /// @dev Only admin can do this
    /// @param period The lock period in block number, default is seven day's block count
    ///
    function setLockPeriod(uint64 period) public onlyOwner {
        _poolLockPeriod = period;
    }

    function setUnlockPeriod(uint64 period) public onlyOwner {
        _poolUnlockPeriod = period;
    }

    /// @param count Vote cfx count, unit is cfx
    function setCfxCountOfOneVote(uint256 count) public onlyOwner {
        CFX_COUNT_OF_ONE_VOTE = count;
        CFX_VALUE_OF_ONE_VOTE = count * 1 ether;
    }

    function setBridge(address bridgeAddress) public onlyOwner {
        _bridgeAddress = bridgeAddress;
        birdgeAddrSetted = true;
    }

    function setPoolName(string memory name) public onlyOwner {
        poolName = name;
    }

    function setVotingEscrow(address _votingEscrow) public onlyOwner {
        votingEscrow = _votingEscrow;
    }

    // ======================== bridge methods =====================

    function unstakeLen() public view returns (uint256) {
        return unstakeQueue.end - unstakeQueue.start;
    }

    function firstUnstakeVotes() public view returns (uint256) {
        if (unstakeQueue.end == unstakeQueue.start) {
            return 0;
        }
        return unstakeQueue.items[unstakeQueue.start].votes;
    }

    function setPoolAPY(uint256 apy) public onlyBridge {
        _poolAPY = apy;
    }

    function handleUnlockedIncrease(
        uint256 votePower
    ) public payable onlyBridge {
        require(
            msg.value == votePower * CFX_VALUE_OF_ONE_VOTE,
            "msg.value should be votePower * 1000 ether"
        );
        withdrawableCfx += msg.value;
        _updatePoolShot();
    }

    function handleCrossingVotes(uint256 votePower) public onlyBridge {
        require(
            crossingVotes >= votePower,
            "crossingVotes should be greater than votePower"
        );
        crossingVotes -= votePower;
    }

    function handleUnstakeTask() public onlyBridge returns (uint256) {
        UnstakeQueue.Node memory node = unstakeQueue.dequeue();
        return node.votes;
    }

    // receive interest
    function receiveInterest() public payable onlyBridge {}

    fallback() external payable {}
}