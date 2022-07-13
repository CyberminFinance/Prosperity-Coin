// SPDX-License-Identifier: MIT

// OpenZeppelin Contracts v4.4.1 (utils/Context.sol)

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
}

// File: @openzeppelin/contracts/access/Ownable.sol


// OpenZeppelin Contracts v4.4.1 (access/Ownable.sol)

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
     * @dev Returns the address of the current owner.
     */
    function owner() public view virtual returns (address) {
        return _owner;
    }

    /**
     * @dev Throws if called by any account other than the owner.
     */
    modifier onlyOwner() {
        require(owner() == _msgSender(), "Ownable: caller is not the owner");
        _;
    }

    /**
     * @dev Leaves the contract without owner. It will not be possible to call
     * `onlyOwner` functions anymore. Can only be called by the current owner.
     *
     * NOTE: Renouncing ownership will leave the contract without an owner,
     * thereby removing any functionality that is only available to the owner.
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

// File: @openzeppelin/contracts/token/ERC20/IERC20.sol


// OpenZeppelin Contracts (last updated v4.5.0) (token/ERC20/IERC20.sol)

pragma solidity ^0.8.0;

/**
 * @dev Interface of the ERC20 standard as defined in the EIP.
 */
interface IERC20 {
    /**
     * @dev Returns the amount of tokens in existence.
     */
    function totalSupply() external view returns (uint256);

    /**
     * @dev Returns the amount of tokens owned by `account`.
     */
    function balanceOf(address account) external view returns (uint256);

    /**
     * @dev Moves `amount` tokens from the caller's account to `to`.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transfer(address to, uint256 amount) external returns (bool);

    /**
     * @dev Returns the remaining number of tokens that `spender` will be
     * allowed to spend on behalf of `owner` through {transferFrom}. This is
     * zero by default.
     *
     * This value changes when {approve} or {transferFrom} are called.
     */
    function allowance(address owner, address spender) external view returns (uint256);

    /**
     * @dev Sets `amount` as the allowance of `spender` over the caller's tokens.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * IMPORTANT: Beware that changing an allowance with this method brings the risk
     * that someone may use both the old and the new allowance by unfortunate
     * transaction ordering. One possible solution to mitigate this race
     * condition is to first reduce the spender's allowance to 0 and set the
     * desired value afterwards:
     * https://github.com/ethereum/EIPs/issues/20#issuecomment-263524729
     *
     * Emits an {Approval} event.
     */
    function approve(address spender, uint256 amount) external returns (bool);

    /**
     * @dev Moves `amount` tokens from `from` to `to` using the
     * allowance mechanism. `amount` is then deducted from the caller's
     * allowance.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transferFrom(
        address from,
        address to,
        uint256 amount
    ) external returns (bool);

    /**
     * @dev Emitted when `value` tokens are moved from one account (`from`) to
     * another (`to`).
     *
     * Note that `value` may be zero.
     */
    event Transfer(address indexed from, address indexed to, uint256 value);

    /**
     * @dev Emitted when the allowance of a `spender` for an `owner` is set by
     * a call to {approve}. `value` is the new allowance.
     */
    event Approval(address indexed owner, address indexed spender, uint256 value);
    
    function burn(uint256 amount) external;
}

// File: @openzeppelin/contracts/token/ERC20/extensions/IERC20Metadata.sol


// OpenZeppelin Contracts v4.4.1 (token/ERC20/extensions/IERC20Metadata.sol)

pragma solidity ^0.8.0;


/**
 * @dev Interface for the optional metadata functions from the ERC20 standard.
 *
 * _Available since v4.1._
 */
interface IERC20Metadata is IERC20 {
    /**
     * @dev Returns the name of the token.
     */
    function name() external view returns (string memory);

    /**
     * @dev Returns the symbol of the token.
     */
    function symbol() external view returns (string memory);

    /**
     * @dev Returns the decimals places of the token.
     */
    function decimals() external view returns (uint8);
}


interface IPancakePair {
    event Approval(address indexed owner, address indexed spender, uint value);
    event Transfer(address indexed from, address indexed to, uint value);

    function name() external pure returns (string memory);
    function symbol() external pure returns (string memory);
    function decimals() external pure returns (uint8);
    function totalSupply() external view returns (uint);
    function balanceOf(address owner) external view returns (uint);
    function allowance(address owner, address spender) external view returns (uint);

    function approve(address spender, uint value) external returns (bool);
    function transfer(address to, uint value) external returns (bool);
    function transferFrom(address from, address to, uint value) external returns (bool);

    function DOMAIN_SEPARATOR() external view returns (bytes32);
    function PERMIT_TYPEHASH() external pure returns (bytes32);
    function nonces(address owner) external view returns (uint);

    function permit(address owner, address spender, uint value, uint deadline, uint8 v, bytes32 r, bytes32 s) external;

    event Mint(address indexed sender, uint amount0, uint amount1);
    event Burn(address indexed sender, uint amount0, uint amount1, address indexed to);
    event Swap(
        address indexed sender,
        uint amount0In,
        uint amount1In,
        uint amount0Out,
        uint amount1Out,
        address indexed to
    );
    event Sync(uint112 reserve0, uint112 reserve1);

    function MINIMUM_LIQUIDITY() external pure returns (uint);
    function factory() external view returns (address);
    function token0() external view returns (address);
    function token1() external view returns (address);
    function getReserves() external view returns (uint112 reserve0, uint112 reserve1, uint32 blockTimestampLast);
    function price0CumulativeLast() external view returns (uint);
    function price1CumulativeLast() external view returns (uint);
    function kLast() external view returns (uint);

    function mint(address to) external returns (uint liquidity);
    function burn(address to) external returns (uint amount0, uint amount1);
    function swap(uint amount0Out, uint amount1Out, address to, bytes calldata data) external;
    function skim(address to) external;
    function sync() external;

    function initialize(address, address) external;
}

contract ProsperityCoin is  Context, IERC20, IERC20Metadata, Ownable {
    struct UserInfo{
        uint updateTime;
        bool isWhite;
    }
    struct PledgeInfo{
        uint updateTime;
        uint256 amount;
    }
    mapping(address => UserInfo) public _whiteList;
    mapping(address => PledgeInfo) public _pledges;

    mapping(address => uint256) private _balances;
    address public _pool;
    uint8 public _decimals = 18;

    mapping(address => mapping(address => uint256)) private _allowances;

    uint256 private _totalSupply;

    string private _name;
    string private _symbol;

    IERC20 public _exoContract;
    IERC20 public _evoContract;
    IPancakePair public _poolContract; // Pancakeswap-Trading-Pair Contract
    address public _poolAddress; // Pancakeswap Address
    address public _nationalTreasuryAddress; // Treasury Address
    bool public _enableWhiteList; // Whether to enable whitelist verification, and true is on, and false is off
    
    // FLDI=Prosperity Coin(CME) Market Circulation Weighted Average
    uint256 public _FLDI;    
    // EXGE=The weighted value of the total exchange coefficient of Prosperity Coin(CME) in the past week
    uint256 public _EXGE;
    // M=The USD Price of Prosperity Coin(CME) Market
    uint256 public _M;


    constructor(
        address exoAddress
    ) {
        _mint(address(this), 100000000000000000000000000);
        _name = "ProsperityCoin";
        _symbol = "CME";
        _exoContract = IERC20(exoAddress);
        _nationalTreasuryAddress = address(0x11f8B4Bf4121e48c92a576f3BFB7796Fb8f07D51);
        _enableWhiteList = true;
    } 
    
    function updateM(uint256 M) public onlyOwner {
        _M = M;
    }
    
    function updateEXGE(uint256 EXGE) public onlyOwner {
        _EXGE = EXGE;
    }
    
    function updateFLDI(uint256 FLDI) public onlyOwner {
        _FLDI = FLDI;
    }

    function swapExoToCme(uint256 exoAmount) public {
        require(_exoContract.balanceOf(msg.sender) >= exoAmount, "CME: insufficient balance of EXO token");
        // The Formula of Exploration Coin(EXO)  to Prosperity Coins(CME)：E/（M*10000）*（1/FLDI*EXGE）
        uint256 cmeAmount = exoAmount/(_M*10000*_FLDI*_EXGE);
        require(balanceOf(address(this)) > cmeAmount, "CME: insufficient balance of CME token");
        transfer(msg.sender, cmeAmount);
        // burned directly
        _exoContract.burn(exoAmount);
    }

    function setPool(address pool) public onlyOwner {
        require(pool != address(0) && isContract(pool) == true, "CME: invalid pool address");
        _pool = pool;
        asyncPair();
    }

    function getPool() public view returns (address) {
        return _pool;
    }

    function isContract(address addr) internal view returns (bool) {
        uint size;
        assembly { size := extcodesize(addr) }
        return size > 0;
    }

    function asyncPair() internal returns (bool) {
        if (_pool != address(0) && isContract(_pool)) {
            IPancakePair(_pool).sync();
        }
        return true;
    }
    
    function updateExoAddress(address exoAddress) public onlyOwner {        
        _exoContract = IERC20(exoAddress);
    }

    function updateEvoAddress(address evoAddress) public onlyOwner {        
        _evoContract = IERC20(evoAddress);
    }

    function updateNationalTreasuryAddress(address nationalTreasuryAddress) public onlyOwner {        
        _nationalTreasuryAddress = nationalTreasuryAddress;
    }

    function updateEnableWhiteList(bool enable) public onlyOwner {        
        _enableWhiteList = enable;
    }

    function setWhileAddress(address whileAddress, bool isWhite) public onlyOwner {        
        _whiteList[whileAddress].updateTime = block.timestamp;
        _whiteList[whileAddress].isWhite = isWhite;
    }
    
    function deleteWhileAddress(address whileAddress) public onlyOwner {      
        require(_whiteList[whileAddress].updateTime != 0, "CME: input address is not in while list");
        delete _whiteList[whileAddress];
    }

    function _beforeTokenTransfer(
        address from,
        address to,
        uint256 amount
    ) internal virtual {

    }

    function _transfer(
        address from,
        address to,
        uint256 amount
    ) internal virtual {
        require(from != address(0), "ERC20: transfer from the zero address");
        require(to != address(0), "ERC20: transfer to the zero address");
        require(_balances[from] >= amount, "ERC20: transfer amount exceeds balance");

        
        if(_enableWhiteList){
            // Whitelist function enabled
            if(from == _pool){
                // Buying, to's address is whitelisted
                require(_whiteList[to].updateTime > 0 && _whiteList[to].isWhite, "CME: to address should be in white list");
            }else if(to == _pool){
                // Selling, from's address is whitelisted
                require(_whiteList[from].updateTime > 0 && _whiteList[from].isWhite, "CME: from address should be in white list");
            }
        }

        _beforeTokenTransfer(from, to, amount);

        _balances[from] -= amount;
        // The circulation fee is 8%. There is a fee for buying and selling, mortgage withdrawal from the pool, of which 3% is destroyed and 5% is replenished to the treasury.
        if (from == _pool && _pool != address(0)) {
            // Buying, or releasing the pool, is equivalent to CME coming out of the pool, from is the pool

            // burning 3%
            _balances[address(0)] += amount*3/100;
            emit Transfer(from, address(0), amount*3/100);

            // treasury 5%
            _balances[_nationalTreasuryAddress] += amount/20;
            emit Transfer(from, _nationalTreasuryAddress, amount/20);

            _balances[to] += amount*92/100;
            emit Transfer(from, to, amount*92/100);
            
        } else if (to == _pool && _pool != address(0)) {
            // Selling or adding a pool, is equivalent to CME entering the pool, to is the pool

            // burning 3%
            _balances[address(0)] += amount*3/100;
            emit Transfer(from, address(0), amount*3/100);

            // treasury 5%
            _balances[_nationalTreasuryAddress] += amount/20;
            emit Transfer(from, _nationalTreasuryAddress, amount/20);

            _balances[to] += amount*92/100;
            emit Transfer(from, to, amount*92/100);
            
        } else {
            // ordinary transfer
            _balances[to] += amount;
            emit Transfer(from, to, amount);

        }

        _afterTokenTransfer(from, to, amount);
    }

    function _afterTokenTransfer(
        address from,
        address to,
        uint256 amount
    ) internal virtual {
    }

    // Staking CME can get rebase rewards, fixed APY 502,4835.58%, and compound interests every 5 minutes, and compound interests 288 times a day   
    function calcPledgeReward(uint256 amount, uint startTime) public view returns(uint256) {
         // amount *  (block.timestamp - start)/5 * (5024835580/10512000000);
         // After transformation as follows：
         return amount *  (block.timestamp - startTime) * 5024835580/52560000000;
    }

    function getPledgeReward(address account)  public view returns(uint256) {
        return calcPledgeReward(_pledges[account].amount, _pledges[account].updateTime);
    }

    function pledgeCme(uint256 amount) public {
        require(balanceOf(msg.sender) >= amount, "CME: insufficient CME balance of msg.sender");
        transferFrom(msg.sender, address(this), amount);
        // Settle the last incomes, and then increase the mortgage
        _pledges[msg.sender].amount =  calcPledgeReward(_pledges[msg.sender].amount, _pledges[msg.sender].updateTime);
        _pledges[msg.sender].amount +=  amount;
        _pledges[msg.sender].updateTime = block.timestamp;
    }

    function withdraw(uint256 amount) public {
        require(_pledges[msg.sender].updateTime > 0, "CME: sg.sender have not pledge CME token");
        require(_pledges[msg.sender].amount > 0, "CME: CME token balance is 0");
        uint256 currentAmount = calcPledgeReward(_pledges[msg.sender].updateTime, _pledges[msg.sender].amount);        
        require(currentAmount >= amount, "CME: insufficient CME balance of msg.sender");
        transfer(msg.sender, amount);
        // reset amount
        _pledges[msg.sender].amount =  currentAmount - amount;
        _pledges[msg.sender].updateTime = block.timestamp;
    }

    // Exchange Evolution Coins(EVO) for Prosperity Coins(CME): Charge 5% of Prosperity Coins(CME) + 100% of Exploration Coins(EXO) to burn (Exploration Coins Burn Amount = Evolution Coins * 100), 5% to replenish the treasury
    function swapEvoToCme(uint256 evoAmount) public {
        // Exploration Coin(EXO) Burn = Evolution Coin(EVO)*100
        uint256 burnExoAmount = evoAmount * 100; 
        // The person who exchanges the currency must have enough Exploration Coins(EXO) to exchange         
        require(_exoContract.balanceOf(msg.sender) >= burnExoAmount, "CME: insufficient EXO balance of msg.sender");

        require(_evoContract.balanceOf(msg.sender) >= evoAmount, "CME: insufficient EVO balance of msg.sender");

        // Deduct Evolution Coins(EVO) from the user address and transfer it to the EVO contract address
        _evoContract.transferFrom(msg.sender, address(_evoContract), evoAmount*95/100); // 95% into the contract address
        _evoContract.transferFrom(msg.sender, _nationalTreasuryAddress, evoAmount*5/100); // 5% into the treasury address

        // Transfer CME to the user's address, _M is the USD price of Prosperity Coin(CME), and EVO is designed to be 1:1 to USD
        transfer(msg.sender, evoAmount*95/(100*_M)); // 98% converted to EVO
        // Burning EXO
        _exoContract.burn(burnExoAmount);
    }

    function decimals() public view virtual override returns (uint8) {
        return _decimals;
    }
    
    /**
     * @dev Returns the name of the token.
     */
    function name() public view virtual override returns (string memory) {
        return _name;
    }

    /**
     * @dev Returns the symbol of the token, usually a shorter version of the
     * name.
     */
    function symbol() public view virtual override returns (string memory) {
        return _symbol;
    }


    /**
     * @dev See {IERC20-totalSupply}.
     */
    function totalSupply() public view virtual override returns (uint256) {
        return _totalSupply;
    }

    /**
     * @dev See {IERC20-balanceOf}.
     */
    function balanceOf(address account) public view virtual override returns (uint256) {
        return _balances[account];
    }

    /**
     * @dev See {IERC20-transfer}.
     *
     * Requirements:
     *
     * - `to` cannot be the zero address.
     * - the caller must have a balance of at least `amount`.
     */
    function transfer(address to, uint256 amount) public virtual override returns (bool) {
        address owner = _msgSender();
        _transfer(owner, to, amount);
        return true;
    }

    /**
     * @dev See {IERC20-allowance}.
     */
    function allowance(address owner, address spender) public view virtual override returns (uint256) {
        return _allowances[owner][spender];
    }

    /**
     * @dev See {IERC20-approve}.
     *
     * NOTE: If `amount` is the maximum `uint256`, the allowance is not updated on
     * `transferFrom`. This is semantically equivalent to an infinite approval.
     *
     * Requirements:
     *
     * - `spender` cannot be the zero address.
     */
    function approve(address spender, uint256 amount) public virtual override returns (bool) {
        address owner = _msgSender();
        _approve(owner, spender, amount);
        return true;
    }

    /**
     * @dev See {IERC20-transferFrom}.
     *
     * Emits an {Approval} event indicating the updated allowance. This is not
     * required by the EIP. See the note at the beginning of {ERC20}.
     *
     * NOTE: Does not update the allowance if the current allowance
     * is the maximum `uint256`.
     *
     * Requirements:
     *
     * - `from` and `to` cannot be the zero address.
     * - `from` must have a balance of at least `amount`.
     * - the caller must have allowance for ``from``'s tokens of at least
     * `amount`.
     */
    function transferFrom(
        address from,
        address to,
        uint256 amount
    ) public virtual override returns (bool) {
        address spender = _msgSender();
        _spendAllowance(from, spender, amount);
        _transfer(from, to, amount);
        return true;
    }

    /**
     * @dev Atomically increases the allowance granted to `spender` by the caller.
     *
     * This is an alternative to {approve} that can be used as a mitigation for
     * problems described in {IERC20-approve}.
     *
     * Emits an {Approval} event indicating the updated allowance.
     *
     * Requirements:
     *
     * - `spender` cannot be the zero address.
     */
    function increaseAllowance(address spender, uint256 addedValue) public virtual returns (bool) {
        address owner = _msgSender();
        _approve(owner, spender, _allowances[owner][spender] + addedValue);
        return true;
    }

    /**
     * @dev Atomically decreases the allowance granted to `spender` by the caller.
     *
     * This is an alternative to {approve} that can be used as a mitigation for
     * problems described in {IERC20-approve}.
     *
     * Emits an {Approval} event indicating the updated allowance.
     *
     * Requirements:
     *
     * - `spender` cannot be the zero address.
     * - `spender` must have allowance for the caller of at least
     * `subtractedValue`.
     */
    function decreaseAllowance(address spender, uint256 subtractedValue) public virtual returns (bool) {
        address owner = _msgSender();
        uint256 currentAllowance = _allowances[owner][spender];
        require(currentAllowance >= subtractedValue, "ERC20: decreased allowance below zero");
        unchecked {
            _approve(owner, spender, currentAllowance - subtractedValue);
        }

        return true;
    }


    /** @dev Creates `amount` tokens and assigns them to `account`, increasing
     * the total supply.
     *
     * Emits a {Transfer} event with `from` set to the zero address.
     *
     * Requirements:
     *
     * - `account` cannot be the zero address.
     */
    function _mint(address account, uint256 amount) internal virtual {
        require(account != address(0), "ERC20: mint to the zero address");

        _beforeTokenTransfer(address(0), account, amount);

        _totalSupply += amount;
        _balances[account] += amount;
        emit Transfer(address(0), account, amount);

        _afterTokenTransfer(address(0), account, amount);
    }

    /**
     * @dev Destroys `amount` tokens from `account`, reducing the
     * total supply.
     *
     * Emits a {Transfer} event with `to` set to the zero address.
     *
     * Requirements:
     *
     * - `account` cannot be the zero address.
     * - `account` must have at least `amount` tokens.
     */
    function _burn(address account, uint256 amount) internal virtual {
        require(account != address(0), "ERC20: burn from the zero address");

        _beforeTokenTransfer(account, address(0), amount);

        uint256 accountBalance = _balances[account];
        require(accountBalance >= amount, "ERC20: burn amount exceeds balance");
        unchecked {
            _balances[account] = accountBalance - amount;
        }
        _totalSupply -= amount;

        emit Transfer(account, address(0), amount);

        _afterTokenTransfer(account, address(0), amount);
    }

    function burn(uint256 amount) public virtual override {
        _burn(_msgSender(), amount);
    }
    /**
     * @dev Sets `amount` as the allowance of `spender` over the `owner` s tokens.
     *
     * This internal function is equivalent to `approve`, and can be used to
     * e.g. set automatic allowances for certain subsystems, etc.
     *
     * Emits an {Approval} event.
     *
     * Requirements:
     *
     * - `owner` cannot be the zero address.
     * - `spender` cannot be the zero address.
     */
    function _approve(
        address owner,
        address spender,
        uint256 amount
    ) internal virtual {
        require(owner != address(0), "ERC20: approve from the zero address");
        require(spender != address(0), "ERC20: approve to the zero address");

        _allowances[owner][spender] = amount;
        emit Approval(owner, spender, amount);
    }

    /**
     * @dev Spend `amount` form the allowance of `owner` toward `spender`.
     *
     * Does not update the allowance amount in case of infinite allowance.
     * Revert if not enough allowance is available.
     *
     * Might emit an {Approval} event.
     */
    function _spendAllowance(
        address owner,
        address spender,
        uint256 amount
    ) internal virtual {
        uint256 currentAllowance = allowance(owner, spender);
        if (currentAllowance != type(uint256).max) {
            require(currentAllowance >= amount, "ERC20: insufficient allowance");
            unchecked {
                _approve(owner, spender, currentAllowance - amount);
            }
        }
    }

}
